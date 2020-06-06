open classical

#check @em

def U (p : Prop) (x : Prop) : Prop := x = true ∨ p
def V (p : Prop) (x : Prop) : Prop := x = false ∨ p

lemma exU : ∀ (p:Prop), ∃ (x : Prop), U p x :=
begin
  intros p, existsi true, left, reflexivity
end


lemma exV : ∀ (p:Prop), ∃ (x : Prop), V p x :=
begin
  intros p, existsi false, left, reflexivity
end

def u (p : Prop) := some (exU p)
def v (p : Prop) := some (exV p)

lemma u_def : ∀ (p : Prop), U p (u p) :=
begin
  intros p, apply some_spec (exU p)
end

lemma v_def : ∀ (p : Prop), V p (v p) :=
begin
  intros p, apply some_spec (exV p)
end

lemma not_uv_or_p : ∀(p:Prop), (u p ≠ v p) ∨ p :=
begin
  intros p, cases (u_def p) with H1 H1, cases (v_def p) with H2 H2,
  { left, rewrite H1, rewrite H2, intros H, have H3 : (true ↔ false),
    {rewrite <- H}, cases H3 with H3 H4, apply H3, constructor},
  {right, assumption},
  {right, assumption}
end

lemma p_implies_uv : ∀ (p : Prop), p → u p = v p := sorry
