require "option_parser"
require "./frontend"
require "./lean_backend"
require "./ir_printer"
require "./verifier"

module CrystalLean
  class NodePrinter < Crystal::Visitor
    def initialize(@io : IO)
    end

    def visit_any(node)
      @io.puts "#{node.class.name} : #{node.type?} : #{node.to_s.inspect}"
      true
    end

    def visit(node)
      true
    end
  end

  module CLI
    private VERSION = {{ read_file("#{__DIR__}/../../shard.yml").split("\n").find { |line| line.starts_with?("version: ") }.split.last }}

    HELP = <<-TEXT
      crystal-lean #{VERSION}
      Translate a restricted, typed Crystal function into a Lean model.

      Usage:
        crystal-lean translate SOURCE.cr [-o OUTPUT.lean] [--check]
        crystal-lean inspect SOURCE.cr
        crystal-lean verify SOURCE.cr --proof PROOF.lean --theorem NAME
          [--contract SPEC.lean --statement NAME] [--lean PATH]
        crystal-lean --help | --version

      Commands:
        translate  Emit the generated Lean model. No algorithm recognition.
        inspect    Print the typed method and the lowered intermediate representation.
        verify     Check a Lean theorem, optionally requiring an independent contract.

      The generated model uses fuel; out-of-fuel means inconclusive, not success.
      With --contract, Lean checks the theorem type and its axiom dependencies.
      Crystal-to-Lean correspondence is not proved.
      Also available as: crystal lean <command> [options]
      TEXT

    private def self.source_file!(args : Array(String), usage : String) : String
      raise "#{usage}\nExpected exactly one source file." unless args.size == 1
      args[0]
    end

    private def self.load_function(source_path : String) : Frontend::Result
      Frontend.new.lower(File.read(source_path), File.expand_path(source_path))
    end

    private def self.check_output!(source : String, output : String) : Nil
      same = File.expand_path(output) == File.expand_path(source)
      same ||= File.exists?(output) && File.same?(output, source, follow_symlinks: true)
      raise "Output path must differ from input path" if same
    end

    private def self.translate(args : Array(String)) : Nil
      output_path : String? = nil
      check = false
      help = false
      parser = OptionParser.new do |p|
        p.banner = "Usage: crystal-lean translate SOURCE.cr [-o OUTPUT.lean] [--check]"
        p.on("-o PATH", "--output=PATH", "Write generated Lean code to PATH") { |v| output_path = v }
        p.on("--check", "Check -o against fresh translation without writing") { check = true }
        p.on("-h", "--help", "Show this help") { help = true }
      end
      parser.parse(args)
      if help
        puts parser
        return
      end
      path = source_file!(args, parser.to_s)
      raise "--check requires -o OUTPUT.lean" if check && output_path.nil?
      check_output!(path, output_path.not_nil!) if output_path
      lean = LeanBackend.new.render(load_function(path).function)
      if (output = output_path)
        if check
          unless File.file?(output) && File.read(output) == lean
            raise "Generated Lean differs from #{output}; rerun translate without --check"
          end
          puts "Generated Lean matches #{output}."
        else
          File.write(output, lean)
        end
      else
        STDOUT << lean
      end
    end

    private def self.inspect_source(args : Array(String)) : Nil
      help = false
      parser = OptionParser.new do |p|
        p.banner = "Usage: crystal-lean inspect SOURCE.cr"
        p.on("-h", "--help", "Show this help") { help = true }
      end
      parser.parse(args)
      if help
        puts parser
        return
      end
      path = source_file!(args, parser.to_s)
      result = load_function(path)
      puts "CRYSTAL_PATH: #{ENV["CRYSTAL_PATH"]}"
      puts "Function: #{result.function.name}"
      print_ast(result.definition)
      puts "Intermediate representation:"
      IRPrinter.new(STDOUT).print(result.function)
    end

    private def self.print_ast(node : Crystal::Def) : Nil
      puts "#{node.name} : #{node.type?}"
      puts node
      puts "Typed AST:"
      node.body.accept(NodePrinter.new(STDOUT))
    end

    private def self.verify(args : Array(String)) : Nil
      lean_bin = ENV["LEAN"]? || "lean"
      proof_path : String? = nil
      theorem : String? = nil
      contract_path : String? = nil
      statement : String? = nil
      help = false
      parser = OptionParser.new do |p|
        p.banner = "Usage: crystal-lean verify SOURCE.cr --proof PROOF.lean --theorem NAME [--contract SPEC.lean --statement NAME] [--lean PATH]"
        p.on("--lean=PATH", "Path to the Lean 4 executable") { |v| lean_bin = v }
        p.on("--proof=PATH", "Lean proof declarations to check") { |v| proof_path = v }
        p.on("--theorem=NAME", "Lean declaration to inspect, e.g. MyNamespace.my_theorem") { |v| theorem = v }
        p.on("--contract=PATH", "Independent Lean specification of the generated model") { |v| contract_path = v }
        p.on("--statement=NAME", "Proposition defined in --contract") { |v| statement = v }
        p.on("-h", "--help", "Show this help") { help = true }
      end
      parser.parse(args)
      if help
        puts parser
        return
      end
      path = source_file!(args, parser.to_s)
      proof_file = proof_path
      theorem_name = theorem
      raise "--proof is required; supply Lean declarations describing the intended property" unless proof_file
      raise "--theorem is required; name the declaration to inspect" unless theorem_name
      if contract_path.nil? != statement.nil?
        raise "--contract and --statement must be supplied together"
      end
      contract = if (contract_file = contract_path) && (contract_statement = statement)
                   {path: contract_file, statement: contract_statement}
                 end
      model = LeanBackend.new.render(load_function(path).function)
      Verifier.verify!(model, proof_file, theorem_name, lean_bin, contract)
      if contract
        puts "Lean accepted #{theorem_name} for contract #{contract[:statement]}."
      else
        puts "Lean accepted #{theorem_name}; its statement and axiom dependencies are shown above."
        puts "Any listed axioms are assumptions; inspect the theorem statement and axiom report."
        puts "The tool does not establish that this declaration specifies the source, proves termination, or uses the generated model."
      end
      puts "Crystal-to-Lean translation is not formally verified. Out-of-fuel is inconclusive."
    end

    def self.run(args : Array(String)) : Int32
      if args.empty? || args == ["-h"] || args == ["--help"] || args == ["help"]
        puts HELP
        return 0
      end
      if args == ["-v"] || args == ["--version"] || args == ["version"]
        puts "crystal-lean #{VERSION}"
        return 0
      end
      args = args.dup
      command = args.shift
      case command
      when "translate" then translate(args)
      when "verify"    then verify(args)
      when "inspect"   then inspect_source(args)
      else
        raise "Unknown command: #{command}\nRun 'crystal-lean --help' for usage."
      end
      0
    rescue ex : Crystal::CodeError
      STDERR.puts ex
      1
    rescue ex
      STDERR.puts "crystal-lean: #{ex.message}"
      1
    end
  end
end
