#!/usr/bin/env ruby
# frozen_string_literal: true

require "json"
require "pathname"
require "time"

def parse_args(argv)
  output = nil
  i = 0
  while i < argv.length
    case argv[i]
    when "--output"
      i += 1
      output = argv[i]
    else
      raise "unknown argument: #{argv[i]}"
    end
    i += 1
  end
  raise "--output is required" if output.nil? || output.empty?

  output
end

def module_name_from(pathname, lean_root)
  relative = pathname.relative_path_from(lean_root).to_s.sub(/\.lean\z/, "")
  relative.split("/").join(".")
end

def parse_namespace_token(token, current_namespace)
  return token if token.include?(".") || current_namespace.nil? || current_namespace.empty?

  "#{current_namespace}.#{token}"
end

def scan_declarations(pathname, lean_root)
  module_name = module_name_from(pathname, lean_root)
  declarations = []
  namespace_stack = []

  pathname.each_line.with_index(1) do |line, line_number|
    stripped = line.strip

    if (match = stripped.match(/^namespace\s+([^\s]+)/))
      namespace_stack << parse_namespace_token(match[1], namespace_stack.last)
      next
    end

    if stripped.match?(/^end(?:\s+[^\s]+)?$/)
      namespace_stack.pop unless namespace_stack.empty?
      next
    end

    match = stripped.match(/^(?:protected\s+)?(theorem|lemma|def|structure|class|abbrev)\s+([^\s\(\:\{\[\:=]+)/)
    next unless match

    kind = match[1]
    name = match[2]
    namespace_name = namespace_stack.last
    full_name =
      if name.include?(".") || namespace_name.nil? || namespace_name.empty?
        name
      else
        "#{namespace_name}.#{name}"
      end

    declarations << {
      kind: kind,
      name: name,
      full_name: full_name,
      module: module_name,
      path: pathname.relative_path_from(lean_root.parent).to_s,
      line: line_number
    }
  end

  declarations
end

output_path = Pathname.new(parse_args(ARGV)).expand_path
repo_root = Pathname.new(__dir__).join("../..").expand_path
lean_root = repo_root.join("lean4")
lakefile = lean_root.join("lakefile.lean").read
toolchain = lean_root.join("lean-toolchain").read.strip

package_name = lakefile[/package\s+"([^"]+)"/, 1] || "Omega"
package_version = lakefile[/version\s*:=\s*v!"([^"]+)"/, 1]
mathlib_ref = lakefile[/require\s+"leanprover-community"\s*\/\s*"mathlib"\s*@\s*git\s*"([^"]+)"/, 1]

module_files =
  [lean_root.join("Omega.lean")] +
  Dir.glob(lean_root.join("Omega/**/*.lean").to_s).sort.map { |path| Pathname.new(path) }
declarations = module_files.flat_map { |path| scan_declarations(path, lean_root) }
decls_by_module = declarations.group_by { |decl| decl[:module] }

modules = module_files.map do |path|
  module_name = module_name_from(path, lean_root)
  {
    name: module_name,
    path: path.relative_path_from(repo_root).to_s,
    declaration_count: decls_by_module.fetch(module_name, []).length
  }
end

manifest = {
  schema_version: 1,
  generated_at: Time.now.utc.iso8601,
  git: {
    sha: `git -C #{repo_root} rev-parse HEAD`.strip,
    tag: ENV["RELEASE_TAG"].to_s.empty? ? nil : ENV["RELEASE_TAG"]
  },
  package: {
    name: package_name,
    version: package_version,
    entry_module: "Omega",
    lean_toolchain: toolchain,
    mathlib: mathlib_ref
  },
  stats: {
    module_count: modules.length,
    declaration_count: declarations.length
  },
  modules: modules,
  declarations: declarations
}

output_path.dirname.mkpath
output_path.write(JSON.pretty_generate(manifest) + "\n")
