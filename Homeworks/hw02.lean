section hw
  variable {p q r : Prop}

  /- Classical.em is not required: -/
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨λ ⟨⟨hp, hq⟩, hr⟩ ↦ ⟨hp, ⟨hq, hr⟩⟩,
  λ ⟨hp, ⟨hq, hr⟩⟩ ↦ ⟨⟨hp, hq⟩, hr⟩⟩

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨
  λ h ↦
  have right := λ r ↦ Or.inr (Or.inr r)
  have left := λ hpq ↦
    Or.elim hpq
    Or.inl
    (λ hq ↦ Or.inr (Or.inl hq))
  Or.elim h left right,

  λ h ↦
  have left hp := Or.inl (Or.inl hp)
  have right hqr :=
    Or.elim hqr
    (λ hq ↦ Or.inl (Or.inr hq))
    Or.inr
  Or.elim h left right
  ⟩

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨
  λ h ↦
  ⟨Or.elim h Or.inl (λ ⟨hq, _⟩ ↦ Or.inr hq),
  Or.elim h Or.inl (λ ⟨_, hr⟩ ↦ Or.inr hr)⟩,

  λ ⟨hpq, hpr⟩ ↦
  Or.elim hpq Or.inl
  (λ hq ↦ Or.elim hpr Or.inl (λ hr ↦ Or.inr ⟨hq, hr⟩))
  ⟩

  example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨
  λ f ⟨hp, hq⟩ ↦ f hp hq,
  λ f hp hq ↦ f ⟨hp, hq⟩
  ⟩

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨
  λ f ↦ ⟨λ hp ↦ f (Or.inl hp), λ hq ↦ f (Or.inr hq)⟩,
  λ ⟨fp, fq⟩ ↦ λ h ↦ Or.elim h fp fq
  ⟩

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨
  λ f ↦ ⟨λ hp ↦ f (Or.inl hp), λ hq ↦ f (Or.inr hq)⟩,
  λ ⟨hnp, hnq⟩ ↦ λ hpq ↦ Or.elim hpq hnp hnq
  ⟩

  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ h ↦ Or.elim h (λ hnp ⟨hp, _⟩ ↦ hnp hp) (λ hnq ⟨_, hq⟩ ↦ hnq hq)

  example : ¬(p ∧ ¬p) :=
  λ ⟨hp, hnp⟩ ↦ hnp hp

  example : p ∧ ¬q → ¬(p → q) :=
  λ ⟨hp, hnq⟩ f ↦ hnq (f hp)

  theorem exp : ¬p → (p → q) :=
  λ hnp hp ↦ False.elim (hnp hp)

  example : (¬p ∨ q) → (p → q) :=
  λ h ↦ Or.elim h exp (λ hq _ ↦ hq)

  example : p ∨ False ↔ p :=
  ⟨
  λ h ↦ Or.elim h (fun x ↦ x) False.elim,
  Or.inl
  ⟩

  example : p ∧ False ↔ False :=
  ⟨
  λ ⟨_, hf⟩ ↦ hf,
  False.elim
  ⟩

  example : (p → q) → (¬q → ¬p) :=
  λ f hnq hp ↦ hnq (f hp)

  /- Classical.em is required: -/
  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ f ↦
    Or.elim (Classical.em p)
    (fun hp ↦ Or.elim (f hp) (λ hq ↦ Or.inl (fun _ ↦ hq)) (λ hr ↦ Or.inr (fun _ ↦ hr)))
    (fun hnp ↦ Or.inl (fun hp ↦ False.elim (hnp hp)))

  example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ f ↦
    Or.elim (Classical.em p)
    (fun hp ↦
      Or.elim (Classical.em q)
      (λ hq ↦ False.elim (f ⟨hp, hq⟩))
      Or.inr
    )
    Or.inl

  theorem neg_imp : ¬(p → q) → p ∧ ¬q :=
  λ f ↦
   Or.elim (Classical.em p)
   (λ hp ↦
    Or.elim (Classical.em q)
    (λ hq ↦ False.elim (f (fun _ ↦ hq)))
    (λ hnq ↦ ⟨hp, hnq⟩)
   )
   (λ hnp ↦ False.elim (f (fun hp ↦ False.elim (hnp hp))))

  example : (p → q) → (¬p ∨ q) :=
  λ f ↦ Or.elim (Classical.em p)
    (fun hp ↦ Or.inr (f hp))
    Or.inl

  example : (¬q → ¬p) → (p → q) :=
  λ f hp ↦
    Or.elim (Classical.em q)
    (fun x ↦ x)
    (fun hnq ↦ False.elim ((f hnq) hp))

  example : p ∨ ¬p := Classical.em p

  example : (((p → q) → p) → p) :=
  λ f ↦
    Or.elim (Classical.em (p → q))
    (fun g ↦ (f g))
    (fun ng ↦ And.left (neg_imp ng))
end hw
