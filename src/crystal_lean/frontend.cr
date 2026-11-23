require "./compiler"
require "./ir"

module CrystalLean
  # Lowers a small closed Crystal language to algorithm-independent IR. This
  # is an experimental translation, not a proof of Crystal's semantics.
  class Frontend
    record Result, definition : Crystal::Def, function : IR::Function

    @vars = {} of String => IR::Ty
    @array_params = Set(String).new
    @writes_array = false
    @return_ty = IR::Ty::I32

    private def fail!(message : String) : NoReturn
      raise "unsupported Crystal: #{message}"
    end

    private def valid_name!(name : String) : Nil
      fail!("identifier #{name.inspect} is outside the supported subset") unless name.matches?(/\A[a-z_][a-zA-Z0-9_]*\z/)
    end

    private def supported_type(name : String?) : IR::Ty?
      case name
      when "Int32"        then IR::Ty::I32
      when "Bool"         then IR::Ty::Bool
      when "Array(Int32)" then IR::Ty::ArrayI32
      end
    end

    private def source_type(node : Crystal::ASTNode?) : IR::Ty
      supported_type(node.try(&.to_s)) || fail!("type #{node} is not supported; use Int32, Bool, or Array(Int32)")
    end

    private def typed_type(node : Crystal::ASTNode) : IR::Ty
      supported_type(node.type?.to_s) || fail!("unsupported or unresolved type #{node.type?} in #{node}")
    end

    private module Syntax
      def self.plain_call?(call : Crystal::Call) : Bool
        !call.block && !call.block_arg && !call.named_args && !call.global?
      end
    end

    private def def_signature(definition : Crystal::Def) : {Array(IR::Param), IR::Ty}
      valid_name!(definition.name)
      if definition.receiver || definition.block_arg || definition.double_splat || definition.splat_index || definition.free_vars ||
         definition.block_arity || definition.abstract? || definition.macro_def? || definition.visibility != Crystal::Visibility::Public ||
         definition.calls_super? || definition.calls_initialize? || definition.calls_previous_def? || definition.uses_block_arg? || definition.assigns_special_var?
        fail!("unsupported method declaration")
      end
      args = [] of IR::Param
      names = Set(String).new
      definition.args.each do |arg|
        valid_name!(arg.name)
        fail!("default, named, splat and annotated parameters are not supported") if arg.default_value || arg.parsed_annotations || arg.external_name != arg.name
        fail!("duplicate argument #{arg.name}") unless names.add?(arg.name)
        args << IR::Param.new(arg.name, source_type(arg.restriction))
      end
      result = source_type(definition.return_type)
      {args, result}
    end

    # This runs before compiler semantic analysis. Unsupported constructs,
    # extra top-level declarations, macros and arbitrary calls must never be
    # handed to the compiler as part of our closed analysis subset.
    private class SyntaxGate < Crystal::Visitor
      def visit_any(node)
        case node
        when Crystal::Expressions, Crystal::Nop, Crystal::Var, Crystal::Assign,
             Crystal::If, Crystal::While, Crystal::Return, Crystal::Not,
             Crystal::BoolLiteral
          # Detailed typing and assignment checks run after semantic analysis.
        when Crystal::NumberLiteral
          raise "unsupported Crystal: only Int32 literals are supported" unless node.kind.to_s == "i32"
        when Crystal::Call
          raise "unsupported Crystal: unsupported call #{node}" unless Syntax.plain_call?(node) && node.obj
          allowed = node.args.size == 1 && !IR::BinaryOp.from_symbol(node.name).nil?
          allowed ||= node.name == "[]" && node.args.size == 1
          allowed ||= node.name == "[]=" && node.args.size == 2
          allowed ||= node.name == "size" && node.args.empty?
          allowed ||= node.name == "-" && node.args.empty?
          raise "unsupported Crystal: unsupported call #{node}" unless allowed
        else
          raise "unsupported Crystal: node #{node.class}: #{node}"
        end
        true
      end

      def visit(node)
        true
      end
    end

    private class ResolvedCall < Crystal::Visitor
      getter defs = [] of Crystal::Def

      def initialize(@name : String); end

      def visit_any(node)
        if node.is_a?(Crystal::Call) && node.obj.nil? && node.name == @name
          node.target_defs.try &.each { |target| @defs << target }
        end
        true
      end

      def visit(node)
        true
      end
    end

    def lower(source : String, filename : String = "input.cr") : Result
      @vars.clear
      @array_params.clear
      @writes_array = false
      parser = Crystal::Parser.new(source)
      parser.filename = filename
      ast = parser.parse
      fail!("expected exactly one top-level method, with no additional code or declarations") unless ast.is_a?(Crystal::Def)
      params, @return_ty = def_signature(ast)
      params.each do |param|
        @vars[param.name] = param.ty
        @array_params.add(param.name) if param.ty == IR::Ty::ArrayI32
      end
      ast.body.accept(SyntaxGate.new)

      # The generated entry point selects the concrete specialization based on
      # the explicit parameter types; it is analyzed, never executed.
      dummy = params.map do |param|
        case param.ty
        when .i32?       then "0_i32"
        when .bool?      then "false"
        when .array_i32? then "[] of Int32"
        else                  raise "BUG: unsupported argument type"
        end
      end.join(", ")
      entry = "\n#{ast.name}(#{dummy})\n"
      calls = ResolvedCall.new(ast.name)
      Compiler.type_check(source + entry, filename).accept(calls)
      fail!("target method must resolve to exactly one typed definition") unless calls.defs.size == 1
      definition = calls.defs.first
      fail!("resolved a different method") unless definition.name == ast.name && definition.location.try(&.filename) == filename
      fail!("unexpected inferred return type #{definition.type?}") unless typed_type(definition) == @return_ty
      # Lowering the typed body also validates types and target definitions.
      body = statements(definition.body, implicit_return: true)
      fail!("array writes require exactly one Array(Int32) parameter") if @writes_array && @array_params.size != 1
      fail!("array writes require returning the array parameter") if @writes_array && @return_ty != IR::Ty::ArrayI32
      function = IR::Function.new(ast.name, params, @return_ty, body)
      Result.new(definition, function)
    end

    private def statements(node : Crystal::ASTNode, implicit_return : Bool = false) : Array(IR::Stmt)
      case node
      when Crystal::Expressions
        result = [] of IR::Stmt
        node.expressions.each_with_index do |expression, index|
          result.concat(statements(expression, implicit_return: implicit_return && index == node.expressions.size - 1))
        end
        fail!("empty function or branch") if implicit_return && node.expressions.empty?
        result
      when Crystal::Nop
        fail!("implicit nil return is not supported") if implicit_return
        [] of IR::Stmt
      when Crystal::Assign
        fail!("assignment used as final return value is not supported") if implicit_return
        target = node.target
        fail!("only local variable assignments are supported") unless target.is_a?(Crystal::Var)
        valid_name!(target.name)
        value = expression(node.value)
        fail!("cannot change local variable type") if @vars.has_key?(target.name) && @vars[target.name] != value.ty
        fail!("array variable assignment is not supported") if value.ty == IR::Ty::ArrayI32
        @vars[target.name] = value.ty
        [IR::Assign.new(target.name, value)] of IR::Stmt
      when Crystal::If
        condition = expression(node.cond)
        fail!("if condition must be Bool; Crystal truthiness is not yet modeled") unless condition.ty == IR::Ty::Bool
        yes = statements(node.then, implicit_return: implicit_return)
        no = statements(node.else, implicit_return: implicit_return)
        [IR::If.new(condition, yes, no)] of IR::Stmt
      when Crystal::While
        fail!("while used as final return value is not supported") if implicit_return
        condition = expression(node.cond)
        fail!("while condition must be Bool") unless condition.ty == IR::Ty::Bool
        body = statements(node.body)
        [IR::While.new(condition, body)] of IR::Stmt
      when Crystal::Return
        value_node = node.exp || fail!("return without a value is not supported")
        expression_statement(value_node, implicit_return: true)
      when Crystal::Call
        if node.name == "[]="
          fail!("array assignment used as final return value is not supported") if implicit_return
          [array_set(node)] of IR::Stmt
        else
          expression_statement(node, implicit_return)
        end
      else
        expression_statement(node, implicit_return)
      end
    end

    private def expression_statement(node : Crystal::ASTNode, implicit_return : Bool) : Array(IR::Stmt)
      value = expression(node)
      if implicit_return
        fail!("return type does not match method declaration") unless value.ty == @return_ty
        validate_array_return!(value)
        [IR::Return.new(value)] of IR::Stmt
      else
        [IR::ExprStmt.new(value)] of IR::Stmt
      end
    end

    private def validate_array_return!(value : IR::Expr) : Nil
      if value.ty == IR::Ty::ArrayI32
        fail!("array return must be an array parameter") unless value.is_a?(IR::Var) && @array_params.includes?(value.name)
      end
    end

    private def array_set(node : Crystal::Call) : IR::ArraySet
      fail!("unsupported array assignment") unless Syntax.plain_call?(node) && node.args.size == 2
      receiver = node.obj
      fail!("array assignment receiver must be an array parameter") unless receiver.is_a?(Crystal::Var) && @array_params.includes?(receiver.name)
      targets = node.target_defs
      fail!("array assignment did not resolve to one method") unless targets && targets.size == 1
      array = expression(receiver)
      index = expression(node.args[0])
      value = expression(node.args[1])
      fail!("array assignment requires Array(Int32), Int32 index and Int32 value") unless array.ty == IR::Ty::ArrayI32 && index.ty == IR::Ty::I32 && value.ty == IR::Ty::I32 && typed_type(node) == IR::Ty::I32
      @writes_array = true
      IR::ArraySet.new(receiver.name, index, value)
    end

    private def expression(node : Crystal::ASTNode) : IR::Expr
      case node
      when Crystal::Expressions
        # Crystal retains parenthesized expressions as an Expressions node.
        # Multi-expression groups would require additional statement sequencing.
        fail!("only a single expression is supported inside parentheses") unless node.expressions.size == 1
        expression(node.expressions.first)
      when Crystal::NumberLiteral
        fail!("only Int32 literals are supported") unless node.kind.to_s == "i32" && typed_type(node) == IR::Ty::I32
        IR::IntLiteral.new(node.integer_value.to_i32)
      when Crystal::BoolLiteral
        IR::BoolLiteral.new(node.value)
      when Crystal::Var
        valid_name!(node.name)
        ty = @vars[node.name]? || fail!("unknown or not-yet-initialized local #{node.name}")
        fail!("variable #{node.name} has changed or unresolved type") unless typed_type(node) == ty
        IR::Var.new(node.name, ty)
      when Crystal::Not
        value = expression(node.exp)
        fail!("boolean not requires Bool") unless value.ty == IR::Ty::Bool
        IR::Unary.new(IR::UnaryOp::Not, value)
      when Crystal::Call
        lower_call(node)
      else
        fail!("expression #{node.class}: #{node}")
      end
    end

    private def lower_call(node : Crystal::Call) : IR::Expr
      fail!("unsupported call") unless Syntax.plain_call?(node) && node.obj
      # Since user-defined methods and class reopenings are rejected by the
      # syntax gate, these calls must resolve to one trusted stdlib definition.
      targets = node.target_defs
      fail!("call #{node} did not resolve to one method") unless targets && targets.size == 1
      left = expression(node.obj.not_nil!)
      case node.name
      when "size"
        fail!("size requires Array(Int32)") unless left.ty == IR::Ty::ArrayI32 && node.args.empty? && typed_type(node) == IR::Ty::I32
        IR::ArraySize.new(left)
      when "[]"
        fail!("indexing requires Array(Int32)") unless left.ty == IR::Ty::ArrayI32 && node.args.size == 1
        right = expression(node.args[0])
        fail!("array index and result must be Int32") unless right.ty == IR::Ty::I32 && typed_type(node) == IR::Ty::I32
        IR::ArrayGet.new(left, right)
      else
        if node.name == "-" && node.args.empty?
          fail!("unary minus requires Int32") unless left.ty == IR::Ty::I32 && typed_type(node) == IR::Ty::I32
          return IR::Unary.new(IR::UnaryOp::Neg, left)
        end
        op = IR::BinaryOp.from_symbol(node.name) || fail!("call #{node.name}")
        fail!("binary operator needs one argument") unless node.args.size == 1
        right = expression(node.args[0])
        if op.eq? || op.ne?
          fail!("equality requires matching Int32 or Bool operands") unless left.ty == right.ty && (left.ty == IR::Ty::I32 || left.ty == IR::Ty::Bool)
        else
          fail!("operator #{node.name} requires Int32 operands") unless left.ty == IR::Ty::I32 && right.ty == IR::Ty::I32
        end
        fail!("unexpected operator return type") unless typed_type(node) == op.result_type
        IR::Binary.new(op, left, right)
      end
    end
  end
end
