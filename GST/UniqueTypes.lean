import GST.Admissible

/-!
# Well-typed terms have unique types

Port of `agda-code/agda/GST/UniqueTypes.agda`.

The implicit arguments are written as a telescope after the colon so that the
equation compiler may refine the two types while matching on the derivations.
-/

namespace GST

open WSLN

theorem svVr : {S : Fset} → {Γ : Cx S} → {A B : Ty} → {x : Atom} →
    (x, A) isIn Γ → (x, B) isIn Γ → A = B
  | _, _, _, _, _, .new, .new => rfl
  | _, _, _, _, _, .new, .old q =>
      absurd q.dom_mem (Fset.not_mem_of_notMem (by assumption))
  | _, _, _, _, _, .old q, .new =>
      absurd q.dom_mem (Fset.not_mem_of_notMem (by assumption))
  | _, _, _, _, _, .old p, .old q => svVr p q

theorem svTy : {S : Fset} → {Γ : Cx S} → {A B : Ty} → {a : Tm0} →
    (Γ ⊢ a ∶ A) → (Γ ⊢ a ∶ B) → A = B
  | _, _, _, _, _, .var q₁, .var q₂ => svVr q₁ q₂
  | _, _, _, _, _, .lam (b := b) (x := x) (h := hx) q hb,
      .lam (x := x') (h := hx') q' hb' =>
      congrArg _ (svTy (rnDerivBody x x' hx hx' b q hb hb') q')
  | _, _, _, _, _, .app p _, .app p' _ => (arrow_inj (svTy p p')).2
  | _, _, _, _, _, .zero, .zero => rfl
  | _, _, _, _, _, .succ _, .succ _ => rfl
  | _, _, _, _, _, .nrec p _ _, .nrec q _ _ => svTy p q

end GST
