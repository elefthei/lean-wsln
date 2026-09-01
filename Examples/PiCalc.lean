import WSLN

/-!
# π-calculus

Port of `agda-code/agda/PiCalc.agda`: a well-scoped locally nameless
representation of π-calculus processes, structural congruence and reduction.
-/

namespace PiCalc

open WSLN

/-! ## Raw expressions -/

/-- Agda: `OpPiC` (PiCalc.agda). -/
inductive Op where
  /-- Agda: `′in′`. Input prefixed process. -/
  | inp : Op
  /-- Agda: `′out′`. Output prefixed process. -/
  | out : Op
  /-- Agda: `′par′`. Parallel composition. -/
  | par : Op
  /-- Agda: `′nu′`. Restriction. -/
  | nu : Op
  /-- Agda: `′repl′`. Replication. -/
  | repl : Op
  /-- Agda: `′null′`. Termination. -/
  | null : Op
  deriving DecidableEq

/-- Agda: `arPiC` (PiCalc.agda). -/
def ar : Op → List Nat
  | .inp => [0, 1]
  | .out => [0, 0, 0]
  | .par => [0, 0]
  | .nu => [1]
  | .repl => [0]
  | .null => []

/-- Agda: `PiC : Sig` (PiCalc.agda). -/
def sig : Sig := ⟨Op, ar⟩

/-- π-calculus expressions in scope `n`; Agda `Trm[ n ]`. -/
abbrev Tm (n : Nat) := WSLN.Trm sig n

instance : DecidableEq sig.Op := inferInstanceAs (DecidableEq Op)

/-! ## Notation -/

/-- Agda: `pattern 𝐢𝐧 a P` (PiCalc.agda). -/
@[match_pattern] def inP {n : Nat} (a : Atom) (P : Tm (n + 1)) : Tm n :=
  .op .inp (.cons (.atom a) (.cons P .nil))

/-- Agda: `pattern 𝐨𝐮𝐭 a b P` (PiCalc.agda). -/
@[match_pattern] def out {n : Nat} (a b : Atom) (P : Tm n) : Tm n :=
  .op .out (.cons (.atom a) (.cons (.atom b) (.cons P .nil)))

/-- Agda: `pattern _∣_ P Q` (PiCalc.agda). -/
@[match_pattern] def par {n : Nat} (P Q : Tm n) : Tm n :=
  .op .par (.cons P (.cons Q .nil))

/-- Agda: `pattern ν P` (PiCalc.agda). -/
@[match_pattern] def nu {n : Nat} (P : Tm (n + 1)) : Tm n := .op .nu (.cons P .nil)

/-- Agda: `pattern ‼ P` (PiCalc.agda). -/
@[match_pattern] def repl {n : Nat} (P : Tm n) : Tm n := .op .repl (.cons P .nil)

/-- Agda: `pattern 𝐎` (PiCalc.agda). -/
@[match_pattern] def O {n : Nat} : Tm n := .op .null .nil

-- Agda writes parallel composition `P ∥ Q`; `∣` is taken by Lean core's `Dvd`
-- notation, so the Lean port uses `∥`.
@[inherit_doc par] scoped infixl:68 " ∥ " => PiCalc.par
@[inherit_doc nu] scoped notation:max "ν " P:max => PiCalc.nu P
@[inherit_doc repl] scoped notation:max "‼ " P:max => PiCalc.repl P
@[inherit_doc O] scoped notation:max "𝐎" => PiCalc.O

/-! ## Well-formed processes -/

/-- Agda: `⊢_proc` (PiCalc.agda). -/
inductive Proc : Tm 0 → Prop where
  /-- Agda: `In`. Input prefixed process. -/
  | In {a x : Atom} {P : Tm 1} (q₀ : x # P) (q₁ : Proc (P[x])) : Proc (inP a P)
  /-- Agda: `Out`. Output prefixed process. -/
  | Out {a b : Atom} {P : Tm 0} (q : Proc P) : Proc (out a b P)
  /-- Agda: `Par`. Parallel composition. -/
  | Par {P Q : Tm 0} (q : Proc P) (q' : Proc Q) : Proc (P ∥ Q)
  /-- Agda: `Nu`. Channel restriction. -/
  | Nu {x : Atom} {P : Tm 1} (q₀ : x # P) (q₁ : Proc (P[x])) : Proc (ν P)
  /-- Agda: `Repl`. Process replication. -/
  | Repl {P : Tm 0} (q : Proc P) : Proc (‼ P)
  /-- Agda: `Null`. Terminated process. -/
  | Null : Proc 𝐎

@[inherit_doc Proc] scoped notation:40 "⊢ " P:41 " proc" => PiCalc.Proc P

/-! ## Structural congruence -/

/-- Agda: `⊢_＝_` (PiCalc.agda). -/
inductive Cong : Tm 0 → Tm 0 → Prop where
  /-- Agda: `Rfl`. -/
  | Rfl {P : Tm 0} (q : ⊢ P proc) : Cong P P
  /-- Agda: `Sym`. -/
  | Sym {P Q : Tm 0} (q : Cong P Q) : Cong Q P
  /-- Agda: `Trs`. -/
  | Trs {P Q R : Tm 0} (q : Cong P Q) (q' : Cong Q R) : Cong P R
  /-- Agda: `InCong`. -/
  | InCong {a x : Atom} {P P' : Tm 1} (q₀ : x # (P, P')) (q₁ : Cong (P[x]) (P'[x])) :
      Cong (inP a P) (inP a P')
  /-- Agda: `OutCong`. -/
  | OutCong {a b : Atom} {P P' : Tm 0} (q : Cong P P') : Cong (out a b P) (out a b P')
  /-- Agda: `ParCong`. -/
  | ParCong {P P' Q Q' : Tm 0} (q : Cong P P') (q' : Cong Q Q') :
      Cong (P ∥ Q) (P' ∥ Q')
  /-- Agda: `NuCong`. -/
  | NuCong {x : Atom} {P P' : Tm 1} (q₀ : x # (P, P')) (q₁ : Cong (P[x]) (P'[x])) :
      Cong (ν P) (ν P')
  /-- Agda: `ReplCong`. -/
  | ReplCong {P P' : Tm 0} (q : Cong P P') : Cong (‼ P) (‼ P')
  /-- Agda: `ParSym`. -/
  | ParSym {P Q : Tm 0} (q : ⊢ P proc) (q' : ⊢ Q proc) : Cong (P ∥ Q) (Q ∥ P)
  /-- Agda: `ParAssoc`. -/
  | ParAssoc {P Q R : Tm 0} (q : ⊢ P proc) (q' : ⊢ Q proc) (q'' : ⊢ R proc) :
      Cong ((P ∥ Q) ∥ R) (P ∥ (Q ∥ R))
  /-- Agda: `ParNull`. -/
  | ParNull {P : Tm 0} (q : ⊢ P proc) : Cong (P ∥ 𝐎) P
  /-- Agda: `νSym`. -/
  | nuSym {x y : Atom} {P : Tm 2} (q₀ : x # y # P) (q₁ : ⊢ P[x][y] proc) :
      Cong (ν (x ． ν (y ． P[x][y]))) (ν (y ． ν (x ． P[x][y])))
  /-- Agda: `νNull`. -/
  | nuNull {x : Atom} : Cong (ν (x ． (𝐎 : Tm 0))) 𝐎
  /-- Agda: `Extrude`. -/
  | Extrude {x : Atom} {P : Tm 1} {Q : Tm 0} (q₀ : x # (P, Q)) (q₁ : ⊢ P[x] proc)
      (q₂ : ⊢ Q proc) : Cong (ν (x ． P[x] ∥ Q)) ((ν P) ∥ Q)
  /-- Agda: `Repl`. -/
  | Repl {P : Tm 0} (q : ⊢ P proc) : Cong (‼ P) (P ∥ ‼ P)

@[inherit_doc Cong] scoped notation:40 "⊢ " P:41 " ＝ " Q:41 => PiCalc.Cong P Q

/-! ## Reduction -/

/-- Agda: `⊢_⟶_` (PiCalc.agda). -/
inductive Red : Tm 0 → Tm 0 → Prop where
  /-- Agda: `Comm`. -/
  | Comm {a b x : Atom} {P : Tm 0} {Q : Tm 1} (q₀ : ⊢ P proc) (q₁ : x # Q)
      (q₂ : ⊢ Q[x] proc) : Red (out a b P ∥ inP a Q) (P ∥ Q[b])
  /-- Agda: `Par`. -/
  | Par {P Q R : Tm 0} (q : Red P Q) (q' : ⊢ R proc) : Red (P ∥ R) (Q ∥ R)
  /-- Agda: `Nu`. -/
  | Nu {x : Atom} {P Q : Tm 1} (q₀ : x # (P, Q)) (q₁ : Red (P[x]) (Q[x])) :
      Red (ν P) (ν Q)
  /-- Agda: `Struc`. -/
  | Struc {P P' Q Q' : Tm 0} (q : Red P Q) (q' : ⊢ P' ＝ P) (q'' : ⊢ Q ＝ Q') :
      Red P' Q'

@[inherit_doc Red] scoped notation:40 "⊢ " P:41 " ⟶ " Q:41 => PiCalc.Red P Q

/-! ## Checks

These `example`s gate the build: they exercise that concretion and abstraction
compute on concrete π-calculus expressions. -/

-- `νNull` on a concrete atom.
example : ⊢ ν ((5 : Atom) ． (𝐎 : Tm 0)) ＝ 𝐎 := .nuNull

-- A `Comm` reduction on concrete atoms; `(‼ 𝐎)[x]` must compute to `‼ 𝐎`.
example : ⊢ (out 1 2 𝐎 ∥ inP 1 (‼ (𝐎 : Tm 1))) ⟶ (𝐎 ∥ ‼ (𝐎 : Tm 0)) :=
  .Comm (x := 0) .Null (by decide) (.Repl .Null)

-- A well-formed input process, using `absConc` to build the binder.
example : ⊢ inP 1 ((3 : Atom) ． (‼ (𝐎 : Tm 0))) proc :=
  .In (x := 3) (fresh_abs 3 _) (by rw [concAbs']; exact .Repl .Null)

-- Replication unfolding, then a structural rewrite.
example : ⊢ ‼ (𝐎 : Tm 0) ＝ (𝐎 ∥ ‼ (𝐎 : Tm 0)) := .Repl .Null

end PiCalc
