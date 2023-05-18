import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "9d37e7354c25ba36adc4784175a26e0a1e7d46ea"

package «united-monoids» {
  -- add package configuration options here
}

@[default_target]
lean_lib «UnitedMonoids» {
  -- add library configuration options here
}

