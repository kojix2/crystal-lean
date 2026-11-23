# Restricted typed, imperative IR. Its data structure is independent of the
# Crystal compiler AST and does not encode particular algorithm names.
module CrystalLean::IR
  enum Ty
    I32
    Bool
    ArrayI32
  end

  record Param, name : String, ty : Ty

  enum BinaryOp
    Add
    Sub
    Mul
    FloorDiv
    Mod
    Eq
    Ne
    Lt
    Le
    Gt
    Ge

    def self.from_symbol(symbol : String) : self?
      BINARY_SYMBOLS[symbol]?
    end

    def symbol : String
      BINARY_SYMBOLS.key_for(self)
    end

    def result_type : Ty
      case self
      in .add?, .sub?, .mul?, .floor_div?, .mod? then Ty::I32
      in .eq?, .ne?, .lt?, .le?, .gt?, .ge?      then Ty::Bool
      end
    end
  end

  private BINARY_SYMBOLS = {
    "+" => BinaryOp::Add, "-" => BinaryOp::Sub, "*" => BinaryOp::Mul,
    "//" => BinaryOp::FloorDiv, "%" => BinaryOp::Mod,
    "==" => BinaryOp::Eq, "!=" => BinaryOp::Ne, "<" => BinaryOp::Lt,
    "<=" => BinaryOp::Le, ">" => BinaryOp::Gt, ">=" => BinaryOp::Ge,
  }

  enum UnaryOp
    Neg
    Not

    def symbol : String
      neg? ? "-" : "!"
    end

    def result_type : Ty
      neg? ? Ty::I32 : Ty::Bool
    end
  end

  abstract class Expr
    abstract def ty : Ty
  end

  class IntLiteral < Expr
    getter value : Int32

    def initialize(@value : Int32); end

    def ty : Ty
      Ty::I32
    end
  end

  class BoolLiteral < Expr
    getter value : Bool

    def initialize(@value : Bool); end

    def ty : Ty
      Ty::Bool
    end
  end

  class Var < Expr
    getter name : String
    getter ty : Ty

    def initialize(@name : String, @ty : Ty); end
  end

  class Binary < Expr
    getter op : BinaryOp
    getter left : Expr
    getter right : Expr

    def initialize(@op : BinaryOp, @left : Expr, @right : Expr); end

    def ty : Ty
      op.result_type
    end
  end

  class Unary < Expr
    getter op : UnaryOp
    getter value : Expr

    def initialize(@op : UnaryOp, @value : Expr); end

    def ty : Ty
      op.result_type
    end
  end

  class ArrayGet < Expr
    getter array : Expr
    getter index : Expr

    def initialize(@array : Expr, @index : Expr); end

    def ty : Ty
      Ty::I32
    end
  end

  class ArraySize < Expr
    getter array : Expr

    def initialize(@array : Expr); end

    def ty : Ty
      Ty::I32
    end
  end

  abstract class Stmt
  end

  class Assign < Stmt
    getter name : String
    getter value : Expr

    def initialize(@name : String, @value : Expr); end
  end

  # Mutation is limited by the frontend to the sole array parameter. Array
  # aliases and reassignment are rejected, so a name identifies its state.
  class ArraySet < Stmt
    getter name : String
    getter index : Expr
    getter value : Expr

    def initialize(@name : String, @index : Expr, @value : Expr); end
  end

  class If < Stmt
    getter cond : Expr
    getter then_branch : Array(Stmt)
    getter else_branch : Array(Stmt)

    def initialize(@cond : Expr, @then_branch : Array(Stmt), @else_branch : Array(Stmt)); end
  end

  class While < Stmt
    getter cond : Expr
    getter body : Array(Stmt)

    def initialize(@cond : Expr, @body : Array(Stmt)); end
  end

  class Return < Stmt
    getter value : Expr

    def initialize(@value : Expr); end
  end

  class ExprStmt < Stmt
    getter value : Expr

    def initialize(@value : Expr); end
  end

  class Function
    getter name : String
    getter params : Array(Param)
    getter return_ty : Ty
    getter body : Array(Stmt)

    def initialize(@name : String, @params : Array(Param), @return_ty : Ty, @body : Array(Stmt)); end
  end
end
