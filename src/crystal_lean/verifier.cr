require "file_utils"

module CrystalLean
  module Verifier
    private PROOF_GATE = {{ read_file("#{__DIR__}/proof_gate.lean") }}

    # Check declarations in a separate module after compiling the proof and,
    # when supplied, its independent contract against the generated model.
    def self.verify!(model : String, proof_path : String, theorem : String, lean_bin : String,
                     contract : NamedTuple(path: String, statement: String)? = nil) : Nil
      check_lean_name!(theorem, "The theorem")
      check_lean_name!(contract[:statement], "The contract statement") if contract
      executable = Process.find_executable(lean_bin) || raise "Unable to find Lean executable: #{lean_bin}"
      executable = File.expand_path(executable)
      proof_path = File.expand_path(proof_path)
      proof = File.read(proof_path)

      directory = File.tempname("crystal-lean", nil)
      Dir.mkdir(directory, 0o700)
      begin
        compile_lean!(executable, directory, "CrystalLeanModel", model, lean_environment(directory))
        if contract
          contract_path = File.expand_path(contract[:path])
          contract_dir = File.dirname(contract_path)
          spec = "import CrystalLeanModel\n" + File.read(contract_path)
          compile_lean!(executable, directory, "CrystalLeanContract", spec, lean_environment(directory, contract_dir))
          imports = "import CrystalLeanContract\n"
          proof_env = lean_environment(directory, contract_dir, File.dirname(proof_path))
          check = "check `#{theorem} `#{contract[:statement]}"
        else
          imports = "import Lean\nimport CrystalLeanModel\n"
          proof_env = lean_environment(directory, File.dirname(proof_path))
          check = "report `#{theorem}"
        end
        compile_lean!(executable, directory, "CrystalLeanProof", imports + proof, proof_env)

        gate_path = File.join(directory, "CrystalLeanCheck.lean")
        File.write(gate_path, PROOF_GATE + "\nopen Lean Elab Command in\n" +
                              "#eval show CommandElabM Unit from CrystalLeanProofGate.#{check}\n")
        run_lean!(executable, directory, [gate_path], proof_env, "the proof check")
      ensure
        FileUtils.rm_rf(directory)
      end
    end

    private def self.check_lean_name!(name : String, label : String) : Nil
      unless name.matches?(/\A[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\z/)
        raise "#{label} must be a plain Lean identifier, e.g. MyNamespace.my_theorem"
      end
    end

    private def self.lean_environment(directory : String, *import_paths) : Hash(String, String)
      separator = {% if flag?(:win32) %} ';' {% else %} ':' {% end %}
      prior = (ENV["LEAN_PATH"]? || "").split(separator).reject(&.empty?)
      paths = [directory] + import_paths.to_a + prior
      {"LEAN_PATH" => paths.map { |path| File.expand_path(path) }.uniq.join(separator)}
    end

    private def self.compile_lean!(executable : String, directory : String, name : String,
                                   contents : String, env : Hash(String, String)) : Nil
      source = File.join(directory, "#{name}.lean")
      compiled = File.join(directory, "#{name}.olean")
      File.write(source, contents)
      run_lean!(executable, directory, ["-o", compiled, source], env, name)
      raise "Lean did not produce #{name}.olean" unless File.file?(compiled)
    end

    private def self.run_lean!(executable : String, directory : String, args : Array(String),
                               env : Hash(String, String), stage : String) : Nil
      status = Process.run(executable, ["--root=#{directory}"] + args, env: env, output: STDOUT, error: STDERR)
      raise "Lean rejected #{stage} (exit #{status.exit_code})" unless status.success?
    rescue ex : IO::Error
      raise "Unable to run Lean executable: #{executable} (#{ex.message})"
    end
  end
end
