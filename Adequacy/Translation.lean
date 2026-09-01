import Adequacy.Nameful

/-!
# Translating nameful terms to locally nameless terms

Port of `agda-code/agda/Adequacy/Translation.agda`.

Locally nameless terms over a binding signature `Sg` are in bijection with
α-equivalence classes of nameful terms over `Sg`.

## Scope casts

The Agda source transports translated binders along `symm (+0) : m ≡ m + 0`, because
there `Arg[ n ] (m :: ms)` stores a `Trm[ m + n ]`.  The Lean core port stores
`Trm Sg (n + m)` instead (`WSLN/Term.lean`), so at `n = 0` an arity-`m` argument has
type `Trm Sg (0 + m)`, and `0 + m` does not reduce for a variable `m`.  The single
transport used throughout is therefore `Trm.castScope`, together with the simp set
below; there is deliberately no second transport convention in this file.

## Declaration order

Agda forward-declares `injective` and `surjective` before the size-bounded
`injective≤*`/`surjective≤*` that implement them.  Lean has no forward declarations,
so `injective` appears immediately after the `injectiveLe*` block and `surjective`
immediately after the `surjectiveLe*` block.
-/

namespace Adequacy

open WSLN

/-! ## The scope cast -/

/-- Lean-specific: transport of a term along an equality of scopes.  This replaces
the Agda source's `subst Trm[_] (symm +0)` transports; see the module docstring. -/
def Trm.castScope {Sg : Sig} {m n : Nat} (e : m = n) (t : Trm Sg m) : Trm Sg n := e ▸ t

@[simp] theorem castScope_symm_castScope {Sg : Sig} {m n : Nat} (e : m = n)
    (t : Trm Sg m) : Trm.castScope e.symm (Trm.castScope e t) = t := by cases e; rfl

/-- Lean-specific: `Trm.castScope` is injective, as `substInj` is in the Agda source. -/
theorem castScope_inj {Sg : Sig} {m n : Nat} (e : m = n) {t t' : Trm Sg m}
    (h : Trm.castScope e t = Trm.castScope e t') : t = t' := by cases e; exact h

@[simp] theorem supp_castScope {Sg : Sig} {m n : Nat} (e : m = n) (t : Trm Sg m) :
    supp (Trm.castScope e t) = supp t := by cases e; rfl

@[simp] theorem size_castScope {Sg : Sig} {m n : Nat} (e : m = n) (t : Trm Sg m) :
    (Trm.castScope e t).size = t.size := by cases e; rfl

@[simp] theorem actSb_castScope {Sg : Sig} {m n : Nat} (σ : Sb Sg) (e : m = n)
    (t : Trm Sg m) : σ * Trm.castScope e t = Trm.castScope e (σ * t) := by cases e; rfl

/-! ## Translation of nameful terms to locally nameless terms -/

mutual

/-- Agda: `⟦_⟧` (Adequacy/Translation.agda). -/
def toWS {Sg : Sig} : NomTrm Sg → Trm Sg 0
  | .atom x => .atom x
  | .op o bs => .op o (toWSArg bs)

/-- Agda: `⟦_⟧ᵃ` (Adequacy/Translation.agda). -/
def toWSArg {Sg : Sig} {ms : List Nat} : NomArg Sg ms → Arg Sg 0 ms
  | .nil => .nil
  | .cons (m := m) b bs =>
      .cons (Trm.castScope (Nat.zero_add m).symm (toWSBnd b)) (toWSArg bs)

/-- Agda: `⟦_⟧ᵇ` (Adequacy/Translation.agda). -/
def toWSBnd {Sg : Sig} {m : Nat} : NomBnd Sg m → Trm Sg m
  | .base M => toWS M
  | .abs x b => x ． toWSBnd b

end

@[simp] theorem toWS_atom {Sg : Sig} (x : Atom) :
    toWS (NomTrm.atom x : NomTrm Sg) = .atom x := rfl

@[simp] theorem toWS_op {Sg : Sig} (o : Sg.Op) (bs : NomArg Sg (Sg.ar o)) :
    toWS (NomTrm.op o bs) = .op o (toWSArg bs) := rfl

@[simp] theorem toWSArg_nil {Sg : Sig} :
    toWSArg (NomArg.nil : NomArg Sg []) = .nil := rfl

@[simp] theorem toWSArg_cons {Sg : Sig} {m : Nat} {ms : List Nat} (b : NomBnd Sg m)
    (bs : NomArg Sg ms) :
    toWSArg (NomArg.cons b bs)
      = .cons (Trm.castScope (Nat.zero_add m).symm (toWSBnd b)) (toWSArg bs) := rfl

@[simp] theorem toWSBnd_base {Sg : Sig} (M : NomTrm Sg) :
    toWSBnd (NomBnd.base M) = toWS M := rfl

@[simp] theorem toWSBnd_abs {Sg : Sig} {m : Nat} (x : Atom) (b : NomBnd Sg m) :
    toWSBnd (NomBnd.abs x b) = (x ． toWSBnd b) := rfl

/-! ## Translation of substitutions -/

/-- Agda: `⟦_⟧ˢ` (Adequacy/Translation.agda). -/
def toWSSb {Sg : Sig} (σ : Atom → NomTrm Sg) : Sb Sg := fun x => toWS (σ x)

@[simp] theorem toWSSb_apply {Sg : Sig} (σ : Atom → NomTrm Sg) (x : Atom) :
    toWSSb σ x = toWS (σ x) := rfl

/-- Agda: `⟦:=⟧ˢ` (Adequacy/Translation.agda).

Agda's overloaded `σ ∘/ x := M` is `WSLN.updateFn σ x M` at nameful substitution
type; the `Sb`-typed update on the right keeps its project token `∘/ ≔`. -/
theorem toWSSb_update {Sg : Sig} (σ : Atom → NomTrm Sg) (M : NomTrm Sg) (x y : Atom) :
    toWSSb (updateFn σ x M) y = ((toWSSb σ) ∘/ x ≔ toWS M) y := by
  by_cases h : x = y <;> simp [Sb.update, updateFn, h]

/-! ## Support property -/

mutual

/-- Agda: `⟦supp⟧` (Adequacy/Translation.agda). -/
theorem toWS_supp {Sg : Sig} (M : NomTrm Sg) : supp (toWS M) ⊆ supp M := by
  match M with
  | .atom _ => exact Fset.subset_refl
  | .op _ bs => exact toWSArg_supp bs

/-- Agda: `⟦supp⟧ᵃ` (Adequacy/Translation.agda). -/
theorem toWSArg_supp {Sg : Sig} {ms : List Nat} (bs : NomArg Sg ms) :
    supp (toWSArg bs) ⊆ supp bs := by
  match bs with
  | .nil => exact Fset.subset_refl
  | .cons b bs' =>
      simp only [toWSArg_cons, supp_cons, suppNomArg_cons, supp_castScope]
      exact Fset.union_subset_union (toWSBnd_supp b) (toWSArg_supp bs')

/-- Agda: `⟦supp⟧ᵇ` (Adequacy/Translation.agda). -/
theorem toWSBnd_supp {Sg : Sig} {m : Nat} (b : NomBnd Sg m) :
    supp (toWSBnd b) ⊆ supp b := by
  match b with
  | .base M => exact toWS_supp M
  | .abs x b' =>
      simp only [toWSBnd_abs, suppNomBnd_abs]
      exact Fset.subset_trans (suppAbs x (toWSBnd b'))
        (Fset.subset_trans (toWSBnd_supp b') Fset.subset_union_right)

end

/-! ## Renamings injective on the names of a nameful term -/

/-- Agda: `Inj` (Adequacy/Translation.agda). -/
def Inj {Sg : Sig} (ρ : Rn) (M : NomTrm Sg) : Prop :=
  ∀ {x x' : Atom}, x ∈ supp M → x' ∈ supp M → ρ x = ρ x' → x = x'

/-- Agda: `Injᵃ` (Adequacy/Translation.agda). -/
def InjArg {Sg : Sig} {ms : List Nat} (ρ : Rn) (bs : NomArg Sg ms) : Prop :=
  ∀ {x x' : Atom}, x ∈ supp bs → x' ∈ supp bs → ρ x = ρ x' → x = x'

/-- Agda: `Injᵇ` (Adequacy/Translation.agda). -/
def InjBnd {Sg : Sig} {m : Nat} (ρ : Rn) (b : NomBnd Sg m) : Prop :=
  ∀ {x x' : Atom}, x ∈ supp b → x' ∈ supp b → ρ x = ρ x' → x = x'

/-- Lean-specific: the argument shared by `InjUpdate`, `InjUpdateArg` and
`InjUpdateBnd`, which the Agda source spells out three times. -/
theorem injUpdate_core {A : Type} [FiniteSupport A] (x y : Atom) (a : A) (h : y # a)
    {z z' : Atom} (hz : z ∈ supp a) (hz' : z' ∈ supp a)
    (e : ((x ≔ʳ y) : Rn) z = ((x ≔ʳ y) : Rn) z') : z = z' := by
  have key : ∀ w : Atom, ((x ≔ʳ y) : Rn) w = if x = w then y else w := by
    intro w
    by_cases hw : x = w
    · subst hw; simp
    · rw [Rn.single_neq _ hw]; simp [hw]
  rw [key z, key z'] at e
  by_cases h₁ : x = z
  · by_cases h₂ : x = z'
    · exact h₁.symm.trans h₂
    · rw [if_pos h₁, if_neg h₂] at e
      subst e
      exact absurd hz' (Fset.not_mem_of_notMem h)
  · by_cases h₂ : x = z'
    · rw [if_neg h₁, if_pos h₂] at e
      subst e
      exact absurd hz (Fset.not_mem_of_notMem h)
    · rwa [if_neg h₁, if_neg h₂] at e

/-- Agda: `InjUpdate` (Adequacy/Translation.agda). -/
theorem InjUpdate {Sg : Sig} (x y : Atom) (M : NomTrm Sg) (h : y # M) :
    Inj ((x ≔ʳ y) : Rn) M := fun hz hz' e => injUpdate_core x y M h hz hz' e

/-- Agda: `InjUpdateᵃ` (Adequacy/Translation.agda). -/
theorem InjUpdateArg {Sg : Sig} {ms : List Nat} (x y : Atom) (bs : NomArg Sg ms)
    (h : y # bs) : InjArg ((x ≔ʳ y) : Rn) bs :=
  fun hz hz' e => injUpdate_core x y bs h hz hz' e

/-- Agda: `InjUpdateᵇ` (Adequacy/Translation.agda). -/
theorem InjUpdateBnd {Sg : Sig} {m : Nat} (x y : Atom) (b : NomBnd Sg m) (h : y # b) :
    InjBnd ((x ≔ʳ y) : Rn) b := fun hz hz' e => injUpdate_core x y b h hz hz' e

/-! ## Injective renamings preserve the translation -/

mutual

/-- Agda: `⟦rn⟧` (Adequacy/Translation.agda). -/
theorem toWS_rn {Sg : Sig} (ρ : Rn) (M : NomTrm Sg) (hinj : Inj ρ M) :
    toWS (ρ * M) = ρ * toWS M := by
  match M with
  | .atom _ => rfl
  | .op o bs => exact congrArg (Trm.op o) (toWSArg_rn ρ bs hinj)

/-- Agda: `⟦rn⟧ᵃ` (Adequacy/Translation.agda). -/
theorem toWSArg_rn {Sg : Sig} {ms : List Nat} (ρ : Rn) (bs : NomArg Sg ms)
    (hinj : InjArg ρ bs) : toWSArg (ρ * bs) = ρ * toWSArg bs := by
  match bs with
  | .nil => rfl
  | .cons (m := m) b bs' =>
      have ih₁ := toWSBnd_rn ρ b (fun p p' => hinj (.unionL p) (.unionL p'))
      have ih₂ := toWSArg_rn ρ bs' (fun p p' => hinj (.unionR p) (.unionR p'))
      have h₁ : Trm.castScope (Nat.zero_add m).symm (toWSBnd (ρ * b))
          = ρ * Trm.castScope (Nat.zero_add m).symm (toWSBnd b) :=
        (congrArg (Trm.castScope (Nat.zero_add m).symm) ih₁).trans
          (actSb_castScope (Sb.ofRn ρ) (Nat.zero_add m).symm (toWSBnd b)).symm
      show Arg.cons (Trm.castScope (Nat.zero_add m).symm (toWSBnd (ρ * b)))
            (toWSArg (ρ * bs'))
          = Arg.cons (ρ * Trm.castScope (Nat.zero_add m).symm (toWSBnd b))
            (ρ * toWSArg bs')
      rw [Arg.cons.injEq]
      exact ⟨h₁, ih₂⟩

/-- Agda: `⟦rn⟧ᵇ` (Adequacy/Translation.agda). -/
theorem toWSBnd_rn {Sg : Sig} {m : Nat} (ρ : Rn) (b : NomBnd Sg m) (hinj : InjBnd ρ b) :
    toWSBnd (ρ * b) = ρ * toWSBnd b := by
  match b with
  | .base M => exact toWS_rn ρ M hinj
  | .abs x b' =>
      have f : ∀ z, z ∈ supp (toWSBnd b') → ¬ (x = z) → ¬ (ρ x = ρ z) := by
        intro z hz hne he
        exact hne (hinj (.unionL .single) (.unionR (toWSBnd_supp b' hz)) he)
      calc toWSBnd (ρ * NomBnd.abs x b')
          = (ρ x ． ρ * toWSBnd b') := by
              rw [rnNomBnd_abs, toWSBnd_abs,
                toWSBnd_rn ρ b' (fun p p' => hinj (.unionR p) (.unionR p'))]
        _ = (ρ x ． ((ρ ∘/ x ≔ʳ ρ x) : Rn) * toWSBnd b') := by
              rw [rnRespSupp (ρ ∘/ x ≔ʳ ρ x) ρ (toWSBnd b')
                (fun y _ => updateFn_id ρ x y)]
        _ = ρ * toWSBnd (NomBnd.abs x b') := (rnAbs ρ x (ρ x) (toWSBnd b') f).symm

end

/-! ## Fresh renaming -/

/-- Agda: `freshRn` (Adequacy/Translation.agda). -/
theorem freshRn {Sg : Sig} (x y : Atom) (M : NomTrm Sg) (h : y # M) :
    toWS (((x ≔ʳ y) : Rn) * M) = ((x ≔ʳ y) : Rn) * toWS M :=
  toWS_rn _ M (InjUpdate x y M h)

/-- Agda: `freshRnᵃ` (Adequacy/Translation.agda). -/
theorem freshRnArg {Sg : Sig} {ms : List Nat} (x y : Atom) (bs : NomArg Sg ms)
    (h : y # bs) : toWSArg (((x ≔ʳ y) : Rn) * bs) = ((x ≔ʳ y) : Rn) * toWSArg bs :=
  toWSArg_rn _ bs (InjUpdateArg x y bs h)

/-- Agda: `freshRnᵇ` (Adequacy/Translation.agda). -/
theorem freshRnBnd {Sg : Sig} {m : Nat} (x y : Atom) (b : NomBnd Sg m) (h : y # b) :
    toWSBnd (((x ≔ʳ y) : Rn) * b) = ((x ≔ʳ y) : Rn) * toWSBnd b :=
  toWSBnd_rn _ b (InjUpdateBnd x y b h)

/-! ## Soundness -/

mutual

/-- Agda: `sound` (Adequacy/Translation.agda). -/
theorem sound {Sg : Sig} {M N : NomTrm Sg} (q : M ~ N) : toWS M = toWS N := by
  match q with
  | .atom _ => rfl
  | .op (o := o) q' => exact congrArg (Trm.op o) (soundArg q')

/-- Agda: `soundᵃ` (Adequacy/Translation.agda). -/
theorem soundArg {Sg : Sig} {ms : List Nat} {bs bs' : NomArg Sg ms} (q : bs ~ᵃ bs') :
    toWSArg bs = toWSArg bs' := by
  match q with
  | .nil => rfl
  | .cons (m := m) q₀ q₁ =>
      simp only [toWSArg_cons, Arg.cons.injEq]
      exact ⟨congrArg (Trm.castScope (Nat.zero_add m).symm) (soundBnd q₀), soundArg q₁⟩

/-- Agda: `soundᵇ` (Adequacy/Translation.agda). -/
theorem soundBnd {Sg : Sig} {m : Nat} {b b' : NomBnd Sg m} (q : b ~ᵇ b') :
    toWSBnd b = toWSBnd b' := by
  match q with
  | .base q' => exact sound q'
  | .abs (x := x) (x' := x') (y := y) (b := b₀) (b' := b₀') q₀ q₁ =>
      have hyb : y # b₀ := Fset.notMem_union_left q₁
      have hyb' : y # b₀' := Fset.notMem_union_right q₁
      simp only [toWSBnd_abs]
      calc (x ． toWSBnd b₀)
          = (y ． ((x ≔ʳ y) : Rn) * toWSBnd b₀) :=
              alphaEquiv x y (toWSBnd b₀) (Fset.subset_notMem (toWSBnd_supp b₀) hyb)
        _ = (y ． toWSBnd (((x ≔ʳ y) : Rn) * b₀)) := by rw [freshRnBnd x y b₀ hyb]
        _ = (y ． toWSBnd (((x' ≔ʳ y) : Rn) * b₀')) := by rw [soundBnd q₀]
        _ = (y ． ((x' ≔ʳ y) : Rn) * toWSBnd b₀') := by rw [freshRnBnd x' y b₀' hyb']
        _ = (x' ． toWSBnd b₀') :=
              (alphaEquiv x' y (toWSBnd b₀')
                (Fset.subset_notMem (toWSBnd_supp b₀') hyb')).symm

end

/-! ## Injectivity -/

/-- Lean-specific: renaming `x` to `y` is concretion of the abstraction `x ． t` at
`y`.  The Agda source inlines this step as `updateRn id x y t` composed with
`concAbs x t (𝐚 y)`. -/
theorem concAbsAtom {Sg : Sig} {n : Nat} (x y : Atom) (t : Trm Sg n) :
    ((x ≔ʳ y) : Rn) * t = (x ． t)[y] := by
  rw [conc_atom, ← conc_trm, concAbs x t (Trm.atom y)]
  exact (updateRn Rn.id x y t).symm

mutual

/-- Agda: `injective≤` (Adequacy/Translation.agda). -/
theorem injectiveLe {Sg : Sig} {h : Nat} (M N : NomTrm Sg) (q : M.size ≤ h)
    (q' : N.size ≤ h) (e : toWS M = toWS N) : M ~ N := by
  match M, N with
  | .atom x, .atom _ =>
      simp only [toWS_atom, Trm.atom.injEq] at e
      subst e
      exact .atom x
  | .atom _, .op _ _ => simp at e
  | .op _ _, .atom _ => simp at e
  | .op o bs, .op o' bs' =>
      have hh : 0 < h := by simp only [NomTrm.size_op] at q; omega
      simp only [NomTrm.size_op] at q q'
      simp only [toWS_op] at e
      have ho : o = o' := Trm.op_inj_fst e
      subst ho
      exact .op (injectiveLeArg (h := h - 1) bs bs' (by omega) (by omega) (Trm.op_inj e))
termination_by (h, 0, 0)

/-- Agda: `injective≤ᵃ` (Adequacy/Translation.agda). -/
theorem injectiveLeArg {Sg : Sig} {h : Nat} {ms : List Nat} (bs bs' : NomArg Sg ms)
    (q : bs.size ≤ h) (q' : bs'.size ≤ h) (e : toWSArg bs = toWSArg bs') : bs ~ᵃ bs' := by
  match bs, bs' with
  | .nil, .nil => exact .nil
  | .cons b bs₀, .cons b' bs₀' =>
      simp only [toWSArg_cons, Arg.cons.injEq] at e
      simp only [NomArg.size_cons] at q q'
      exact .cons
        (injectiveLeBnd (h := h) b b' (by omega) (by omega) (castScope_inj _ e.1))
        (injectiveLeArg (h := h) bs₀ bs₀' (by omega) (by omega) e.2)
termination_by (h, 2, ms.length)

/-- Agda: `injective≤ᵇ` (Adequacy/Translation.agda). -/
theorem injectiveLeBnd {Sg : Sig} {h : Nat} {m : Nat} (b b' : NomBnd Sg m)
    (q : b.size ≤ h) (q' : b'.size ≤ h) (e : toWSBnd b = toWSBnd b') : b ~ᵇ b' := by
  match m, b, b' with
  | 0, .base M, .base M' => exact .base (injectiveLe M M' q q' e)
  | _ + 1, .abs x b₀, .abs x' b₀' =>
      obtain ⟨y, hy⟩ := fresh (b₀, b₀')
      have hyb : y # b₀ := Fset.notMem_union_left hy
      have hyb' : y # b₀' := Fset.notMem_union_right hy
      simp only [NomBnd.size_abs] at q q'
      simp only [toWSBnd_abs] at e
      refine .abs ?_ hy
      refine injectiveLeBnd _ _ (sizeRenBndLe b₀ _ q) (sizeRenBndLe b₀' _ q') ?_
      calc toWSBnd (((x ≔ʳ y) : Rn) * b₀)
          = ((x ≔ʳ y) : Rn) * toWSBnd b₀ := freshRnBnd x y b₀ hyb
        _ = (x ． toWSBnd b₀)[y] := concAbsAtom x y (toWSBnd b₀)
        _ = (x' ． toWSBnd b₀')[y] := by rw [e]
        _ = ((x' ≔ʳ y) : Rn) * toWSBnd b₀' := (concAbsAtom x' y (toWSBnd b₀')).symm
        _ = toWSBnd (((x' ≔ʳ y) : Rn) * b₀') := (freshRnBnd x' y b₀' hyb').symm
termination_by (h, 1, m)

end

/-- Agda: `injective` (Adequacy/Translation.agda). -/
theorem injective {Sg : Sig} (M N : NomTrm Sg) (e : toWS M = toWS N) : M ~ N :=
  injectiveLe (h := max M.size N.size) M N (Nat.le_max_left _ _) (Nat.le_max_right _ _) e

/-! ## Surjectivity -/

mutual

/-- Agda: `surjective≤` (Adequacy/Translation.agda). -/
def surjectiveLe {Sg : Sig} {s : Nat} (t : Trm Sg 0) (q : t.size ≤ s) :
    { M : NomTrm Sg // toWS M = t } :=
  match t, q with
  | .var i, _ => absurd i.isLt (Nat.not_lt_zero i.val)
  | .atom x, _ => ⟨.atom x, rfl⟩
  | .op o ts, q =>
      have hh : 0 < s := by simp only [Trm.size_op] at q; omega
      have hq : ts.size ≤ s - 1 := by simp only [Trm.size_op] at q; omega
      let r := surjectiveLeArg (s := s - 1) ts hq
      ⟨.op o r.val, by simp only [toWS_op]; exact congrArg (Trm.op o) r.property⟩
termination_by (s, 0, 0)

/-- Agda: `surjective≤ᵃ` (Adequacy/Translation.agda). -/
def surjectiveLeArg {Sg : Sig} {s : Nat} {ms : List Nat} (ts : Arg Sg 0 ms)
    (q : ts.size ≤ s) : { bs : NomArg Sg ms // toWSArg bs = ts } :=
  match ms, ts, q with
  | [], .nil, _ => ⟨.nil, rfl⟩
  | m :: _, .cons t us, q =>
      have hq : (Trm.castScope (Nat.zero_add m) t).size ≤ s := by
        simp only [Arg.size_cons] at q; simp only [size_castScope]; omega
      have hq' : us.size ≤ s := by simp only [Arg.size_cons] at q; omega
      let rb := surjectiveLeBnd (Trm.castScope (Nat.zero_add m) t) hq
      let rs := surjectiveLeArg us hq'
      ⟨.cons rb.val rs.val, by simp [rb.property, rs.property]⟩
termination_by (s, 2, ms.length)

/-- Agda: `surjective≤ᵇ` (Adequacy/Translation.agda). -/
def surjectiveLeBnd {Sg : Sig} {m s : Nat} (t : Trm Sg m) (q : t.size ≤ s) :
    { b : NomBnd Sg m // toWSBnd b = t } :=
  match m, t, q with
  | 0, t, q =>
      let r := surjectiveLe t q
      ⟨.base r.val, r.property⟩
  | _ + 1, t, q =>
      let xf := fresh t
      let r := surjectiveLeBnd (t[xf.val]) (size_conc_le t xf.val q)
      ⟨.abs xf.val r.val, by
        simp only [toWSBnd_abs, r.property]
        exact absConc xf.val t xf.property⟩
termination_by (s, 1, m)

end

/-- Agda: `surjective` (Adequacy/Translation.agda). -/
def surjective {Sg : Sig} (t : Trm Sg 0) : { M : NomTrm Sg // toWS M = t } :=
  surjectiveLe (s := t.size) t (Nat.le_refl _)

/-! ## Bijection -/

/-- Agda: `⟦_⟧⁻¹` (Adequacy/Translation.agda). -/
def toNom {Sg : Sig} (t : Trm Sg 0) : NomTrm Sg := (surjective t).val

/-- Agda: `bijection` (Adequacy/Translation.agda). -/
theorem bijection {Sg : Sig} (t : Trm Sg 0) : toWS (toNom t) = t := (surjective t).property

/-- Agda: `bijection'` (Adequacy/Translation.agda). -/
theorem bijection₂ {Sg : Sig} (M : NomTrm Sg) : toNom (toWS M) ~ M :=
  injective (toNom (toWS M)) M (bijection (toWS M))

#print axioms bijection

end Adequacy
