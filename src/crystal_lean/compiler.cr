require "compiler/requires"

module CrystalLean
  # The embedded Crystal compiler is used only for parsing and type checking.
  module Compiler
    def self.type_check(source : String, filename : String) : Crystal::ASTNode
      ensure_standard_library!
      compiler = Crystal::Compiler.new
      compiler.no_codegen = true
      compiler.no_cleanup = true
      compiler.compile(Crystal::Compiler::Source.new(filename, source), "unused").node
    end

    # When no explicit path was supplied, query the same Crystal installation
    # used by the user. The verified subset doesn't allow user requires, so
    # omit relative search entries that could shadow the standard prelude.
    private def self.ensure_standard_library! : Nil
      return unless ENV["CRYSTAL_PATH"]?.nil?

      crystal = ENV["CRYSTAL"]? || "crystal"
      expected_version = Crystal::Config.version
      version = IO::Memory.new
      output = IO::Memory.new
      errors = IO::Memory.new
      begin
        version_status = Process.run(crystal, ["--version"], output: version, error: errors)
        unless version_status.success? && version.to_s.split.first(2) == ["Crystal", expected_version]
          actual = version.to_s.lines.first?.try(&.strip).inspect
          raise "Crystal #{expected_version} is required for automatic standard-library discovery; #{crystal} --version returned #{actual}"
        end
        errors.clear
        status = Process.run(crystal, ["env", "CRYSTAL_PATH"], output: output, error: errors)
      rescue ex : IO::Error
        raise "Crystal is required to locate its standard library; set CRYSTAL_PATH or install Crystal #{expected_version} and put it on PATH (#{ex.message})"
      end

      path = output.to_s.strip
      unless status.success? && !path.empty?
        raise "Could not obtain CRYSTAL_PATH from #{crystal} env CRYSTAL_PATH: #{errors.to_s.strip}"
      end
      separator = {% if flag?(:win32) %} ';' {% else %} ':' {% end %}
      entries = path.split(separator).select { |entry| !entry.empty? && Path[entry].absolute? }
      raise "Crystal did not report an absolute standard-library path; set CRYSTAL_PATH explicitly" if entries.empty?
      ENV["CRYSTAL_PATH"] = entries.join(separator)
    end
  end
end
