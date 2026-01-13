import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.WHNFSKY

/-!
# LeanKernel.WHNFDeltaSKY (Phase 22)

Computation-plane δ-reduction (constant unfolding) for weak-head normalization:

* extend the Phase 16 λ-encoded WHNF step to consult a SKY-encoded environment (Phase 21),
* compile to closed SKY combinators via bracket abstraction,
* execute via `SKYExec.reduceFuel` and decode only constructor tags for cross-validation.

This initial phase treats the environment as *already instantiated* at a fixed universe argument list `us`.
Accordingly, `const c us` ignores the `us` field in the expression and looks up `c` in the provided env.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket

namespace WHNFDeltaSKY

open HeytingLean.LoF.LeanKernel.WHNFSKY
open HeytingLean.LoF.LeanKernel.WHNFSKY.L

abbrev L : Type := WHNFSKY.L

/-! ## WHNF step with δ-reduction (β/ζ/δ, left spine) -/

/--
One WHNF step with δ-reduction:

`whnfStepDeltaSky : Env → Expr → Option Expr`

The environment is the Phase 21 Scott-encoded list of declarations.
-/
def whnfStepDeltaSky : L :=
  app .Y <|
    lam "self" <|
      lam "env" <|
        lam "e" <|
          exprCase (v "e")
            (lam "i" optNone)
            (lam "m" optNone)
            (lam "u" optNone)
            (lam "c"
              (lam "us"
                (optCase (app2 EnvironmentSKY.constValue? (v "env") (v "c"))
                  optNone
                  (lam "body" (optSome (v "body"))))))
            (lam "f"
              (lam "a"
                (optCase (app2 (v "self") (v "env") (v "f"))
                  (exprCase (v "f")
                    (lam "i" optNone)
                    (lam "m" optNone)
                    (lam "u" optNone)
                    (lam "c" (lam "us" optNone))
                    (lam "f1" (lam "a1" optNone))
                    (lam "bn"
                      (lam "bi"
                        (lam "ty"
                          (lam "body" (optSome (app2 instantiate1Sky (v "a") (v "body")))))))
                    (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                    (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" optNone)))))
                    (lam "l" optNone))
                  (lam "f'" (optSome (exprApp (v "f'") (v "a")))))))
            (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
            (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
            (lam "bn"
              (lam "bi"
                (lam "ty"
                  (lam "val"
                    (lam "body" (optSome (app2 instantiate1Sky (v "val") (v "body"))))))))
            (lam "l" optNone)

/--
Bounded WHNF with δ-reduction:

`whnfDeltaSky : Env → Nat → Expr → Expr`
-/
def whnfDeltaSky : L :=
  app .Y
    (lam "self"
      (lam "env"
        (lam "fuel"
          (lam "e"
            (natCase (v "fuel")
              (v "e")
              (lam "n"
                (optCase (app2 whnfStepDeltaSky (v "env") (v "e"))
                  (v "e")
                  (lam "e'" (app3 (v "self") (v "env") (v "n") (v "e'"))))))))))

/-! ## Closed compilation and execution helpers -/

def compileClosed? (t : L) : Option Comb :=
  Bracket.Lam.compileClosed? (Var := String) t

def whnfStepDeltaComb? : Option Comb :=
  compileClosed? whnfStepDeltaSky

def whnfDeltaComb? : Option Comb :=
  compileClosed? whnfDeltaSky

def encodeNatComb? (n : Nat) : Option Comb :=
  compileClosed? (Expr.Scott.encodeNat n)

def runWhnfDeltaTagFuel (fuelWhnf fuelReduce : Nat) (us : List (ULevel Unit Unit))
    (env : Environment.Env Nat Unit Unit Unit) (e : Expr Nat Unit Unit Unit) : Option String := do
  let whnf <- whnfDeltaComb?
  let envC <- EnvironmentSKY.envComb? us env
  let fuelC <- encodeNatComb? fuelWhnf
  let eC <- Lean4LeanSKY.Enc.compileExprNatUnit? e
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app whnf envC) fuelC) eC)
  Lean4LeanSKY.Decode.exprTagFuel fuelReduce out

end WHNFDeltaSKY

end LeanKernel
end LoF
end HeytingLean
