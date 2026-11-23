require "json"
require "ecr"
require "./ir"

module CrystalLean
  # Lower the typed, algorithm-independent IR to a self-contained Lean file.
  # The generated program is interpreted with an explicit fuel argument;
  # `outOfFuel` is inconclusive, not a successful termination or exception.
  class LeanBackend
    RUNTIME = {{ read_file("#{__DIR__}/lean_runtime.lean") }}

    def render(function : IR::Function) : String
      params = function.params.map_with_index { |param, i| " (arg#{i} : #{lean_type(param.ty)})" }.join
      bindings = function.params.map_with_index do |param, i|
        "(#{param.name.to_json}, .#{value_constructor(param.ty)} arg#{i})"
      end.join(", ")
      ECR.render "#{__DIR__}/lean_program.ecr"
    end

    private def lean_type(ty : IR::Ty) : String
      case ty
      in .i32?       then "Int"
      in .bool?      then "Bool"
      in .array_i32? then "Array Int"
      end
    end

    private def value_constructor(ty : IR::Ty) : String
      case ty
      in .i32?       then "i32"
      in .bool?      then "bool"
      in .array_i32? then "array"
      end
    end

    private def statements(stmts : Array(IR::Stmt)) : String
      "(.seq [#{stmts.map { |stmt| statement(stmt) }.join(", ")}])"
    end

    private def statement(stmt : IR::Stmt) : String
      case stmt
      when IR::Assign
        "(.assign #{stmt.name.to_json} #{expression(stmt.value)})"
      when IR::ArraySet
        "(.arraySet #{stmt.name.to_json} #{expression(stmt.index)} #{expression(stmt.value)})"
      when IR::If
        "(.ifElse #{expression(stmt.cond)} #{statements(stmt.then_branch)} #{statements(stmt.else_branch)})"
      when IR::While
        "(.whileLoop #{expression(stmt.cond)} #{statements(stmt.body)})"
      when IR::Return
        "(.returnValue #{expression(stmt.value)})"
      when IR::ExprStmt
        "(.expr #{expression(stmt.value)})"
      else
        raise "unsupported IR statement: #{stmt.class}"
      end
    end

    private def expression(expr : IR::Expr) : String
      case expr
      when IR::IntLiteral
        "(.intLit (#{expr.value}))"
      when IR::BoolLiteral
        "(.boolLit #{expr.value})"
      when IR::Var
        "(.variable #{expr.name.to_json})"
      when IR::Binary
        "(.binary .#{operator_name(expr.op)} #{expression(expr.left)} #{expression(expr.right)})"
      when IR::Unary
        "(.unary .#{operator_name(expr.op)} #{expression(expr.value)})"
      when IR::ArrayGet
        "(.arrayGet #{expression(expr.array)} #{expression(expr.index)})"
      when IR::ArraySize
        "(.arraySize #{expression(expr.array)})"
      else
        raise "unsupported IR expression: #{expr.class}"
      end
    end

    # Lean uses the same operator names with a lowercase initial letter.
    private def operator_name(op : IR::BinaryOp | IR::UnaryOp) : String
      op.to_s.camelcase(lower: true)
    end
  end
end
