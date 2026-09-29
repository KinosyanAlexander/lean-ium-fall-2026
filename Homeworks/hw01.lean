section hw
  variable (α β γ δ : Type)

  -- Define any functions with the following types.
  -- If you can't, explain why

  def ex1 : α → β → α := λ a _ ↦ a

  def ex2 : (α → β → γ) → β → α → γ := fun f b a ↦ f a b

  def ex3 : (α → (β → γ)) → (α → β) → α → γ := fun f g a ↦ (f a) (g a)

  def ex4 : ((α → β) → γ) → (β → γ → δ) → (α → β) → α → δ :=
  fun f g h a ↦ g (h a) (f h)

  def ex5 : (α → β) → β → α := sorry
  /-
  Не можем, т.к. никакой редукцией нельзя получить тип α из функции с таргетом типа β
  и элемента типа β. Можно также сослаться на Curry-Howard Correspondence, который мы
  еще будем изучать. Еще аргумент: функция (α → β) → (β → α) умела бы делать для произвольной
  функции функцию, направленную в обратную сторону, что нонсенс. Так что sorry.
  -/

end hw
