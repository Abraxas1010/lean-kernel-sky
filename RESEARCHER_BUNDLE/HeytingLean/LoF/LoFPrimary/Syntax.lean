/-!
# LoFPrimary.Syntax — Spencer–Brown “primary algebra” syntax (foundational scaffold)

This folder formalizes the **syntax** of a Laws of Form–style primary calculus, distinct from the
“LoF-combinator” (K/S/Y) correspondence layer in `LoF/Correspondence/LoFSKY.lean`.

We model the *primary* constructors:

* `void`  : the unmarked state (blank)
* `var`   : a variable placeholder (finite arity `n`)
* `mark`  : crossing / distinction
* `juxt`  : juxtaposition (concatenation)

Re-entry (second-degree equations) is treated separately; see `HeytingLean.LoF.LoFSecond`.
-/

namespace HeytingLean
namespace LoF
namespace LoFPrimary

/-! ## Syntax -/

/-- Primary LoF expressions with `n` free variables. -/
inductive Expr (n : Nat) where
  | void : Expr n
  | var : Fin n → Expr n
  | mark : Expr n → Expr n
  | juxt : Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

namespace Expr

variable {n : Nat}

/-- The marked constant (often written as an empty mark). -/
def marked : Expr n :=
  mark void

end Expr

end LoFPrimary
end LoF
end HeytingLean
