
section propositional
variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro np,
  exact np(p),
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro p,
  by_cases h : P,
  exact h,
  have hboom := p(h),
  by_contradiction hboom,
  exact p(h),
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro nnp,
  by_cases h : P,
  exact h,

  exfalso,
  exact nnp(h),

  intro p,
  intro pboom,
  exact pboom(p),
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro poq,
  cases poq,
  right,
  exact poq,
  left,
  exact poq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hpeq,
  cases hpeq with hp hq,
  split,
  exact hq,
  exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------
inductive Nat
| O : Nat
| succ : Nat → Nat

inductive ListNat 
| nil : ListNat 
| cons : Nat → ListNat → ListNat
open Nat
open ListNat
#check cons O nil
  




theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hnpeq,
  intro p,
  cases hnpeq with np q,
  exfalso,
  exact np(p),
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro poq,
  cases poq with p q,
  intro np,
  exfalso,
  exact np(p),
  intro np,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hptoq,
  intro nq,
  intro p,
  have q := hptoq(p),
  exact nq(q),
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hnqtonp,
  intro p,
  by_cases h : Q,
  exact h,
  have np := hnqtonp(h), 
  exfalso,
  exact np(p),
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro hpq,
  intro nq,
  intro p,
  have q := hpq(p),
  exact nq(q),

  intro hnqnp,
  intro p,
  by_cases q : Q,
  exact q,
  have np := hnqnp(q),
  exfalso,
  exact np(p),
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro pnp,
  apply pnp,
  right,
  intro p,
  apply pnp,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro pqp,
  intro np,
  apply np,
  apply pqp,
  intro p,
  exfalso,
  exact np(p),
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro poq,
  intro npenq,
  cases npenq with np nq,
  cases poq with p q,
  exact np(p),
  exact nq(q),
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro peq,
  intro nponq,
  cases peq with p q,
  cases nponq with np nq,
  exact np(p),
  exact nq(q),
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npeq,
  split,
  intro p,
  apply npeq,
  left,
  exact p,
  intro q,
  apply npeq,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npenq,
  intro poq,
  cases poq with p q,
  cases npenq with np nq,
  exact np(p),
  cases npenq with np nq,
  exact nq(q),
end
theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_cases p : P,
  left,
  intro q,
  apply h,
  split,
  exact p,
  exact q,
  right,
  exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqnp,
  intro peq,
  cases peq with p q,
  cases nqnp with nq np,
  exact nq(q),
  exact np(p),
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro h,
  by_cases p : P,
  left,
  intro q,
  apply h,
  split,
  exact p,
  exact q,
  right,
  exact p,

  intro nqnp,
  intro peq,
  cases peq with p q,
  cases nqnp with nq np,
  exact nq(q),
  exact np(p),
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro npeq,
  split,
  intro p,
  apply npeq,
  left,
  exact p,
  intro q,
  apply npeq,
  right,
  exact q,

  intro npenq,
  intro poq,
  cases poq with p q,
  cases npenq with np nq,
  exact np(p),
  cases npenq with np nq,
  exact nq(q),
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro peqor,
  cases peqor with p qor,
  cases qor with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro peqoper,
  cases peqoper with peq per,
  split,
  cases peq with p q,
  exact p,
  cases peq with p q,
  left,
  exact q,
  cases per with p r,
  split,
  exact p,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro poqer,
  cases poqer with p qor,
  split,
  left,
  exact p,
  left,
  exact p,
  cases qor with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro poqepor,
  cases poqepor with poq por,
  cases poq with p q,
  left,
  exact p,
  cases por with p r,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro peqtor,
  intro p,
  intro q,
  have peq : P ∧ Q,
  split,
  exact p,
  exact q,
  exact peqtor(peq),
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro ptoqtor,
  intro peq,
  cases peq with p q,
  have qtor := ptoqtor(p),
  exact qtor(q),
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro peq,
  cases peq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro peq,
  cases peq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pep,
  cases pep with p p,
  exact p,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pop,
  cases pop with p p,
  exact p,
  exact p,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro nEx,
  intro Axu,
  intro p,
  apply nEx,
  existsi Axu,
  exact p,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro AxnP,
  intro ExP,
  cases ExP with x ExP,
  apply AxnP,
  exact ExP,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro nA,
  by_contradiction hboom,
  by_cases (∃x, ¬P x),
  have ndacerto := hboom(h),
  exact ndacerto,
  apply nA,
  intro u,
  by_contradiction,
  apply hboom,
  existsi u,
  exact h,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
