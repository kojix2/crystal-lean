require "spec"
require "../src/crystal_lean/frontend"

private def simple(name : String) : String
  <<-SOURCE
    def #{name}(value : Int32) : Int32
      if value < 10
        value + 1
      else
        value
      end
    end
    SOURCE
end

describe CrystalLean::Frontend do
  it "returns the typed AST and IR together across repeated analyses" do
    frontend = CrystalLean::Frontend.new
    first = frontend.lower(simple("first_name"))
    f = first.function
    f.name.should eq("first_name")
    f.params.first.ty.should eq(CrystalLean::IR::Ty::I32)
    first.definition.name.should eq("first_name")

    other = frontend.lower(simple("different_algorithm"))
    other.function.name.should eq("different_algorithm")
    other.definition.name.should eq("different_algorithm")

    expect_raises(Exception) { frontend.lower("def extra; 0; end\n" + simple("bad")) }
    frontend.lower(simple("after_failure")).function.name.should eq("after_failure")
  end

  it "lowers while, local assignments, array reads, Bool conditions and Int32 results" do
    source = <<-SOURCE
      def generic_sum(xs : Array(Int32), enabled : Bool) : Int32
        i = 0
        total = 0
        while i < xs.size
          if enabled
            total = total + xs[i]
          end
          i = i + 1
        end
        total
      end
      SOURCE
    f = CrystalLean::Frontend.new.lower(source).function
    f.name.should eq("generic_sum")
    f.params.map(&.ty).should eq([CrystalLean::IR::Ty::ArrayI32, CrystalLean::IR::Ty::Bool])
    f.body.any? { |statement| statement.is_a?(CrystalLean::IR::While) }.should be_true
    f.body.last.should be_a(CrystalLean::IR::Return)
  end

  it "rejects unmodeled constructs instead of silently changing their meaning" do
    unsupported = [
      "def extra; 0; end\n" + simple("one"),
      "struct Int32; def zzz; 0; end; end\n" + simple("two"),
      "def macro_case(x : Int32) : Int32\n  {{ 1 }}\nend",
      "def and_case(x : Bool, y : Bool) : Bool\n  x && y\nend",
      "def alias_case(xs : Array(Int32)) : Int32\n  ys = xs\n  ys[0] = 1\n  1\nend",
      "def multi_write(xs : Array(Int32), ys : Array(Int32)) : Int32\n  xs[0] = ys[0]\n  1\nend",
      "def scalar_return(xs : Array(Int32)) : Int32\n  xs[0] = 1\n  1\nend",
      "def return_set(xs : Array(Int32)) : Int32\n  xs[0] = 1\nend",
      "def truthy_case(x : Int32) : Int32\n  if x; 1; else; 0; end\nend",
      "def helper_call(x : Int32) : Int32\n  puts x\n  x\nend",
      "def wrong_type(x : Int64) : Int64\n  x\nend",
    ]
    unsupported.each do |source|
      expect_raises(Exception) { CrystalLean::Frontend.new.lower(source) }
    end
  end

  it "lowers element writes and returns the mutated array parameter" do
    source = <<-SOURCE
      def replace(xs : Array(Int32), i : Int32) : Array(Int32)
        xs[i] = xs[0]
        xs
      end
      SOURCE
    f = CrystalLean::Frontend.new.lower(source).function
    f.return_ty.should eq(CrystalLean::IR::Ty::ArrayI32)
    set = f.body.first.as(CrystalLean::IR::ArraySet)
    set.name.should eq("xs")
    set.index.should be_a(CrystalLean::IR::Var)
    set.value.should be_a(CrystalLean::IR::ArrayGet)
    f.body.last.as(CrystalLean::IR::Return).value.as(CrystalLean::IR::Var).name.should eq("xs")
  end

  it "retains support for multiple read-only arrays" do
    source = <<-SOURCE
      def two_arrays(xs : Array(Int32), ys : Array(Int32)) : Int32
        xs[0] + ys[0]
      end
      SOURCE
    f = CrystalLean::Frontend.new.lower(source).function
    f.params.size.should eq(2)
  end
end
