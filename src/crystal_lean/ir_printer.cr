require "./ir"

module CrystalLean
  # Human-readable IR for inspect; this is not used for code generation.
  class IRPrinter
    def initialize(@io : IO)
    end

    def print(function : IR::Function) : Nil
      params = function.params.map { |param| "#{param.name}: #{param.ty}" }.join(", ")
      @io.puts "#{function.name}(#{params}) -> #{function.return_ty}"
      print_statements(function.body, 1)
    end

    private def print_statements(statements : Array(IR::Stmt), depth : Int32) : Nil
      prefix = "  " * depth
      statements.each do |stmt|
        case stmt
        when IR::Assign
          @io.puts "#{prefix}#{stmt.name} = #{expression(stmt.value)}"
        when IR::ArraySet
          @io.puts "#{prefix}#{stmt.name}[#{expression(stmt.index)}] = #{expression(stmt.value)}"
        when IR::If
          @io.puts "#{prefix}if #{expression(stmt.cond)}"
          print_statements(stmt.then_branch, depth + 1)
          unless stmt.else_branch.empty?
            @io.puts "#{prefix}else"
            print_statements(stmt.else_branch, depth + 1)
          end
          @io.puts "#{prefix}end"
        when IR::While
          @io.puts "#{prefix}while #{expression(stmt.cond)}"
          print_statements(stmt.body, depth + 1)
          @io.puts "#{prefix}end"
        when IR::Return
          @io.puts "#{prefix}return #{expression(stmt.value)}"
        when IR::ExprStmt
          @io.puts "#{prefix}#{expression(stmt.value)}"
        else
          raise "Unsupported IR statement for inspect: #{stmt.class}"
        end
      end
    end

    private def expression(expr : IR::Expr) : String
      case expr
      when IR::IntLiteral  then expr.value.to_s
      when IR::BoolLiteral then expr.value.to_s
      when IR::Var         then expr.name
      when IR::Binary      then "(#{expression(expr.left)} #{expr.op.symbol} #{expression(expr.right)})"
      when IR::Unary       then "(#{expr.op.symbol}#{expression(expr.value)})"
      when IR::ArrayGet    then "#{expression(expr.array)}[#{expression(expr.index)}]"
      when IR::ArraySize   then "#{expression(expr.array)}.size"
      else                      raise "Unsupported IR expression for inspect: #{expr.class}"
      end
    end
  end
end
