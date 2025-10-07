
class Quiver where
    ob  : Type u
    rel : ob → ob → Type v

class PreCategory extends Quiver where
    id    : (X : ob) → (rel X X)
    comp  : (rel X Y) → (rel Y Z) → (rel X Z)

infixl:80 " ∘ " => PreCategory.comp

class Category extends PreCategory where
    comp_id_l : (f : rel X Y) → (id X ∘ f) = f
    comp_id_r : (f : rel X Y) → (f ∘ id Y) = f
    comp_assoc   : ∀ {X Y Z W : ob} (f : rel W X) (g : rel X Y) (h : rel Y Z),
                (f ∘ g) ∘ h = f ∘ (g ∘ h)

class Dedekind_Notations extends Category where
    inverse : rel X Y → rel Y X
    redidual : rel X Y → rel Y Z → rel X Z
    empty : (X : ob) → (Y : ob) → rel X Y
    universal : (X : ob) → (Y : ob) → rel X Y
    inc : rel X Y → rel X Y → Prop
    cup : rel X Y → rel X Y → rel X Y
    cap : rel X Y → rel X Y → rel X Y
    rpc : rel X Y → rel X Y → rel X Y
    complement : rel X Y → rel X Y
def idr [c : Dedekind_Notations](X:c.ob) := c.id X
def inverse [c : Dedekind_Notations]{X Y:c.ob}(f : c.rel X Y) := c.inverse f
postfix:120 " # " => inverse
infixl:80 " ▹ " => Dedekind_Notations.redidual
def φ [c : Dedekind_Notations] := c.empty
def Δ [c : Dedekind_Notations] := c.universal
infixl:51 " ⊑ " => Dedekind_Notations.inc
infixl:70 " ⊔ " => Dedekind_Notations.cup
infixl:70 " ⊓ " => Dedekind_Notations.cap
infixl:81 " ⇒ " => Dedekind_Notations.rpc
postfix:120 " ᶜ " => Dedekind_Notations.complement

class Dedekind extends Dedekind_Notations where
    inc_refl (f:rel X Y) : f ⊑ f
    inc_trans {f g h : rel X Y} : inc f g → inc g h → inc f h
    inc_antisym {f g : rel X Y}: f ⊑ g → g ⊑ f → f = g
    inc_cap {f g h : rel X Y} : f ⊑ g ⊓ h ↔ f ⊑ g ∧ f ⊑ h
    inc_cup {f g h : rel X Y} : f ⊔ g ⊑ h ↔ f ⊑ h ∧ g ⊑ h
    inc_empty  (f : rel X Y) : φ X Y ⊑ f
    inc_universal (f : rel X Y) : f ⊑ Δ X Y
    inc_rpc {f g h : rel X Y} : f ⊑ g ⇒ h ↔ f ⊓ g ⊑ h
    inv_invol (f : rel X Y) : (f#)# = f
    comp_inv (f : rel X Y) (g : rel Y Z) : (f ∘ g)# = g# ∘ f#
    inc_inv {f g : rel X Y} : f ⊑ g → f# ⊑ g#
    dedekind : f ∘ g ⊓ h ⊑ (f ⊓ h ∘ g#) ∘ (g ⊓ f# ∘ h)
    inc_redidual {f : rel X Y}{g : rel Y Z}{h : rel X Z}  : h ⊑ f ▹ g ↔ f# ∘ h ⊑ g
    is_unit : ob → Prop
    unit_axioms {I : ob}: is_unit I →
      φ I I ≠ idr I ∧ idr I = Δ I I ∧ ∀ X, Δ X I ∘ Δ I X = Δ X X
    incident_pair (X Y:ob):= ∃Z : ob, ∃ (l : rel X Z) (r : rel Y Z),
      l ∘ l# = idr X ∧ r ∘ r# = idr Y ∧ l ∘ r# = φ X Y ∧ (l# ∘ l) ⊔ (r# ∘ r) = idr Z
class Shroder extends Dedekind_Notations where
    inc_refl (f:rel X Y) : f ⊑ f
    inc_trans {f g h : rel X Y} : inc f g → inc g h → inc f h
    inc_antisym {f g : rel X Y}: f ⊑ g → g ⊑ f → f = g
    inc_cap {f g h : rel X Y} : f ⊑ g ⊓ h ↔ f ⊑ g ∧ f ⊑ h
    inc_cup {f g h : rel X Y} : f ⊔ g ⊑ h ↔ f ⊑ h ∧ g ⊑ h
    inc_empty  (f : rel X Y) : φ X Y ⊑ f
    inc_universal (f : rel X Y) : f ⊑ Δ X Y
    inc_rpc {f g h : rel X Y} : f ⊑ g ⇒ h ↔ f ⊓ g ⊑ h
    inv_invol (f : rel X Y) : (f#)# = f
    comp_inv (f : rel X Y) (g : rel Y Z) : (f ∘ g)# = g# ∘ f#
    inc_inv {f g : rel X Y} : f ⊑ g → f# ⊑ g#
    dedekind : f ∘ g ⊓ h ⊑ (f ⊓ h ∘ g#) ∘ (g ⊓ f# ∘ h)
    complement_classic (f : rel X Y) : f ⊔ fᶜ = Δ X Y ∧ f ⊓ fᶜ = φ X Y

def is_unit [c : Dedekind](I:c.ob) := c.is_unit I
def unit_ob [c : Dedekind]:= {I : c.ob // c.is_unit I}
section Dedekind

variable [c : Dedekind]
variable {X Y Z: c.ob}

@[simp] theorem comp_id_l (f:c.rel X Y) : (idr X) ∘ f = f := c.comp_id_l f
@[simp] theorem comp_id_r (f:c.rel X Y) : f ∘ (idr Y) = f := c.comp_id_r f
@[simp] theorem comp_assoc {W:c.ob} (f : c.rel W X) (g : c.rel X Y) (h : c.rel Y Z) :
  f ∘ (g ∘ h) = (f ∘ g) ∘ h := by rw[← c.comp_assoc f g h]
@[simp] theorem inc_refl (f : c.rel X Y) : f ⊑ f := c.inc_refl f
theorem inc_trans {f g h : c.rel X Y} : f ⊑ g → g ⊑ h → f ⊑ h := @c.inc_trans X Y f g h
theorem inc_antisym {f g : c.rel X Y}: f ⊑ g → g ⊑ f → f = g := @c.inc_antisym X Y f g
theorem inc_antisym' {f g : c.rel X Y} : f ⊑ g ∧ g ⊑ f ↔ f = g := by
  apply Iff.intro
  · intro H
    apply inc_antisym H.left H.right
  · intro H
    rw[H]
    simp
theorem inc_cap {f g h : c.rel X Y} : f ⊑ g ⊓ h ↔ f ⊑ g ∧ f ⊑ h := @c.inc_cap X Y f g h
theorem inc_cup {f g h : c.rel X Y} : f ⊔ g ⊑ h ↔ f ⊑ h ∧ g ⊑ h := @c.inc_cup X Y f g h
@[simp] theorem inc_empty  (f : c.rel X Y) : φ X Y ⊑ f := c.inc_empty f
@[simp] theorem inc_universal (f : c.rel X Y) : f ⊑ Δ X Y := c.inc_universal f
theorem inc_rpc {f g h : c.rel X Y} : f ⊑ g ⇒ h ↔ f ⊓ g ⊑ h := @c.inc_rpc X Y f g h
@[simp] theorem inv_invol (f : c.rel X Y) : f## = f := c.inv_invol f
@[simp] theorem comp_inv (f : c.rel X Y) (g : c.rel Y Z) : (f ∘ g)# = g# ∘ f# := c.comp_inv f g
@[simp] theorem inc_inv {f g : c.rel X Y} : f# ⊑ g# ↔ f ⊑ g := by
  apply Iff.intro
  · intro H
    rw[←inv_invol f, ←inv_invol g]
    exact c.inc_inv H
  · exact c.inc_inv
@[simp] theorem dedekind : f ∘ g ⊓ h ⊑ (f ⊓ h ∘ g#) ∘ (g ⊓ f# ∘ h) := c.dedekind
theorem inc_redidual {f : c.rel X Y}{g : c.rel Y Z}{h : c.rel X Z} : h ⊑ f ▹ g ↔ f# ∘ h ⊑ g := @c.inc_redidual X Y Z f g h


@[simp] theorem cap_l (f g : c.rel X Y) : f ⊓ g ⊑ f :=
  (c.inc_cap.mp (c.inc_refl (f ⊓ g))).left
@[simp] theorem cap_r (f g : c.rel X Y) : f ⊓ g ⊑ g :=
  (c.inc_cap.mp (c.inc_refl (f ⊓ g))).right
@[simp] theorem cup_l (f g : c.rel X Y) : f ⊑ f ⊔ g :=
  (c.inc_cup.mp (c.inc_refl (f ⊔ g))).left
@[simp] theorem cup_r (f g : c.rel X Y) : g ⊑ f ⊔ g :=
  (c.inc_cup.mp (c.inc_refl (f ⊔ g))).right
theorem inc_defl : f = f ⊓ g ↔ f ⊑ g := by
  apply Iff.intro
  · intro H
    rw[H]
    simp
  · intro H
    apply c.inc_antisym
    · exact c.inc_cap.mpr ⟨c.inc_refl f, H⟩
    · simp
theorem inc_defr : g = f ⊓ g ↔ g ⊑ f := by
  apply Iff.intro
  · intro H
    rw[H]
    simp
  · intro H
    apply c.inc_antisym
    · exact c.inc_cap.mpr ⟨H, c.inc_refl g⟩
    · simp

@[simp] theorem cap_assoc : f ⊓ (g ⊓ h) = f ⊓ g ⊓ h := by
  apply c.inc_antisym
  · apply c.inc_cap.mpr
    constructor
    · apply c.inc_cap.mpr
      constructor
      · simp
      · apply c.inc_trans
        apply cap_r
        apply cap_l
    · apply c.inc_trans
      apply cap_r
      apply cap_r
  · apply c.inc_cap.mpr
    constructor
    · apply c.inc_trans
      apply cap_l
      apply cap_l
    · apply c.inc_cap.mpr
      constructor
      · apply c.inc_trans
        apply cap_l
        apply cap_r
      · simp
@[simp] theorem cup_assoc : f ⊔ (g ⊔ h) = f ⊔ g ⊔ h := by
  apply c.inc_antisym
  · apply c.inc_cup.mpr
    constructor
    · exact c.inc_trans (cup_l f g) (cup_l (f ⊔ g) h)
    · apply c.inc_cup.mpr
      constructor
      · exact c.inc_trans (cup_r f g) (cup_l (f ⊔ g) h)
      · exact cup_r (f ⊔ g) h
  · apply c.inc_cup.mpr
    constructor
    · apply c.inc_cup.mpr
      constructor
      · apply cup_l
      · exact c.inc_trans (cup_l g h) (cup_r f (g ⊔ h))
    · exact c.inc_trans (cup_r g h) (cup_r f (g ⊔ h))

theorem cap_comm (f g:c.rel X Y): f ⊓ g = g ⊓ f := by
  apply c.inc_antisym
  · apply c.inc_cap.mpr
    constructor
    · exact cap_r f g
    · exact cap_l f g
  · apply c.inc_cap.mpr
    constructor
    · exact cap_r g f
    · exact cap_l g f

theorem cup_comm (f g:c.rel X Y): f ⊔ g = g ⊔ f := by
  apply c.inc_antisym
  · exact c.inc_cup.mpr ⟨cup_r g f, cup_l g f⟩
  · exact c.inc_cup.mpr ⟨cup_r f g, cup_l f g⟩

@[simp] theorem cup_cap_abs (f g:c.rel X Y): f ⊔ (f ⊓ g) = f := by
  apply c.inc_antisym
  · apply c.inc_cup.mpr
    simp
  · simp

@[simp] theorem cap_cup_abs (f g:c.rel X Y): f ⊓ (f ⊔ g) = f := by
  apply c.inc_antisym
  · simp
  · apply c.inc_cap.mpr
    simp

@[simp] theorem cap_idem (f:c.rel X Y): f ⊓ f = f := by
  apply c.inc_antisym
  · simp
  · apply c.inc_cap.mpr
    simp

@[simp] theorem cup_idem (f:c.rel X Y): f ⊔ f = f := by
  apply c.inc_antisym
  · apply c.inc_cup.mpr
    simp
  · simp

theorem cap_inc_compat (f f' g g':c.rel X Y) :
  f ⊑ f' → g ⊑ g' → f ⊓ g ⊑ f' ⊓ g' := by
  intro H H'
  apply c.inc_cap.mpr
  constructor
  · apply c.inc_trans
    apply cap_l
    apply H
  · apply c.inc_trans
    apply cap_r
    apply H'

theorem cap_inc_compat_l (f g g':c.rel X Y) :
  g ⊑ g' → f ⊓ g ⊑ f ⊓ g' := by
  intro H
  apply cap_inc_compat
  simp
  apply H

theorem cap_inc_compat_r (f f' g:c.rel X Y) :
  f ⊑ f' → f ⊓ g ⊑ f' ⊓ g := by
  intro H
  apply cap_inc_compat
  apply H
  simp

theorem cup_inc_compat (f f' g g':c.rel X Y) :
  f ⊑ f' → g ⊑ g' → f ⊔ g ⊑ f' ⊔ g' := by
  intro H H'
  apply c.inc_cup.mpr
  constructor
  · apply c.inc_trans
    apply H
    apply cup_l
  · apply c.inc_trans
    apply H'
    apply cup_r

theorem cup_inc_compat_l (f g g':c.rel X Y) :
  g ⊑ g' → f ⊔ g ⊑ f ⊔ g' := by
  intro H
  apply cup_inc_compat
  apply c.inc_refl
  apply H
theorem cup_inc_compat_r {f f' g:c.rel X Y} :
  f ⊑ f' → f ⊔ g ⊑ f' ⊔ g := by
  intro H
  apply cup_inc_compat
  apply H
  apply c.inc_refl

@[simp] theorem cap_empty (f:c.rel X Y) : f ⊓ φ X Y = φ X Y := by
  apply c.inc_antisym
  all_goals simp
@[simp] theorem empty_cap (f:c.rel X Y) : φ X Y ⊓ f = φ X Y := by
  rw[cap_comm]
  simp
@[simp] theorem cup_empty (f:c.rel X Y) : f ⊔ φ X Y = f := by
  apply c.inc_antisym
  · apply c.inc_cup.mpr
    all_goals simp
  · simp
@[simp] theorem empty_cup (f:c.rel X Y) : φ X Y ⊔ f = f := by
  rw[cup_comm]
  simp
@[simp] theorem cap_universal (f:c.rel X Y) : f ⊓ Δ X Y = f := by
  apply c.inc_antisym
  · simp
  · apply c.inc_cap.mpr
    all_goals simp
@[simp] theorem universal_cap (f:c.rel X Y) : Δ X Y ⊓ f = f := by
  rw[cap_comm]
  simp
@[simp] theorem cup_universal (f:c.rel X Y) : f ⊔ Δ X Y = Δ X Y := by
  apply c.inc_antisym
  all_goals simp
@[simp] theorem universal_cup (f:c.rel X Y) : Δ X Y ⊔ f = Δ X Y := by
  rw[cup_comm]
  simp

theorem inc_lower {f g:c.rel X Y} :
  f = g ↔ (∀ h, h ⊑ f ↔ h ⊑ g) := by
  apply Iff.intro
  · intro H h
    rw[H]
  · intro H
    apply c.inc_antisym
    · apply (H f).mp
      simp
    · apply (H g).mpr
      simp

theorem inc_upper {f g:c.rel X Y} :
  f = g ↔ (∀ h, f ⊑ h ↔ g ⊑ h) := by
  apply Iff.intro
  · intro H h
    rw[H]
  · intro H
    apply c.inc_antisym
    · apply (H g).mpr
      apply c.inc_refl
    · apply (H f).mp
      apply c.inc_refl

theorem cap_cup_distr_l (f g h:c.rel X Y) :
  f ⊓ (g ⊔ h) = (f ⊓ g) ⊔ (f ⊓ h) := by
  apply inc_upper.mpr
  intro a
  apply Iff.intro
  · intro H
    rw[cap_comm , cap_comm f h, c.inc_cup, ← c.inc_rpc, ← c.inc_rpc, ← c.inc_cup, c.inc_rpc, cap_comm]
    apply H
  · intro H
    rw[cap_comm , cap_comm f h, c.inc_cup, ← c.inc_rpc, ← c.inc_rpc, ← c.inc_cup, c.inc_rpc, cap_comm] at H
    apply H

theorem cap_cup_distr_r (f g h:c.rel X Y) :
  (f ⊔ g) ⊓ h = (f ⊓ h) ⊔ (g ⊓ h) := by
  repeat rw[cap_comm _ h]
  apply cap_cup_distr_l

theorem cup_cap_distr_l (f g h:c.rel X Y) :
  f ⊔ (g ⊓ h) = (f ⊔ g) ⊓ (f ⊔ h) := by
  rw[cap_cup_distr_l]
  conv  => rhs;rw[cap_comm, cap_cup_abs]
  rw[cap_cup_distr_r, ← cup_assoc, cup_cap_abs]

theorem cup_cap_distr_r (f g h:c.rel X Y) :
  (f ⊓ g) ⊔ h = (f ⊔ h) ⊓ (g ⊔ h) := by
  repeat rw[cup_comm _ h]
  apply cup_cap_distr_l

theorem cap_cup_unique (f g h:c.rel X Y) :
  f ⊓ g = f ⊓ h → f ⊔ g = f ⊔ h → g = h := by
  intro H1 H2
  rw[← cup_cap_abs g f, cap_comm, H1, cup_cap_distr_l, cup_comm, H2, cup_comm, cup_comm g h, ← cup_cap_distr_l, H1, cap_comm, cup_cap_abs]


theorem rel_unique : φ X Y = Δ X Y → ∀ f g:c.rel X Y, f = g := by
  intro H f g
  apply c.inc_antisym
  all_goals(
    apply c.inc_trans
    · apply inc_universal
    · rw[← H]
      simp)
theorem comp_inc_compat_ab_ab' {f:c.rel X Y} {g g':c.rel Y Z} :
  g ⊑ g' → f ∘ g ⊑ f ∘ g' := by
  intro H
  rw[← inv_invol f]
  apply inc_redidual.mp
  apply inc_trans H
  apply inc_redidual.mpr
  simp

theorem comp_inc_compat_ab_a'b {f f':c.rel X Y} {g:c.rel Y Z} :
  f ⊑ f' → f ∘ g ⊑ f' ∘ g := by
  intro H
  rw[← inc_inv]
  simp
  apply comp_inc_compat_ab_ab'
  simp
  assumption

theorem comp_inc_compat (f f':c.rel X Y) (g g':c.rel Y Z) :
  f ⊑ f' → g ⊑ g' → f ∘ g ⊑ f' ∘ g' := by
  intro H H'
  apply inc_trans
  · apply comp_inc_compat_ab_a'b H
  · apply comp_inc_compat_ab_ab' H'

theorem comp_inc_compat_ab_a {f:c.rel X Y} {g:c.rel Y Y} :
  g ⊑ idr Y → f ∘ g ⊑ f := by
  intro H
  conv => rhs; rw[← comp_id_r f]
  apply comp_inc_compat_ab_ab' H

theorem comp_inc_compat_a_ab {f:c.rel X Y} {g:c.rel Y Y} :
  idr Y ⊑ g → f ⊑ f ∘ g := by
  intro H
  conv => lhs; rw[← comp_id_r f]
  apply comp_inc_compat_ab_ab' H

theorem comp_inc_compat_ab_b {f:c.rel X X} {g:c.rel X Y} :
  f ⊑ idr X → f ∘ g ⊑ g := by
  intro H
  conv => rhs; rw[← comp_id_l g]
  apply comp_inc_compat_ab_a'b H

theorem comp_inc_compat_b_ab {f:c.rel X X} {g:c.rel X Y} :
  idr X ⊑ f → g ⊑ f ∘ g := by
  intro H
  conv => lhs; rw[← comp_id_l g]
  apply comp_inc_compat_ab_a'b H

theorem inv_move : f = g# ↔ f# = g := by
  apply Iff.intro
  · intro H
    rw[H]
    simp
  · intro H
    rw[← inv_invol f, ← inv_invol g]
    rw[H]
    simp

@[simp] theorem comp_inv_inv (f:c.rel X Y) (g:c.rel Y Z) :
  (g# ∘ f#)# = f ∘ g := by
  rw[comp_inv, inv_invol, inv_invol]
theorem inv_inc_move {f:c.rel X Y}{g:c.rel Y X} :
  f ⊑ g# ↔ f# ⊑ g := by
  rw[← inv_invol f, inc_inv]
  simp
@[simp] theorem inv_invol' : f# = g# ↔ f = g := by
  rw[inv_move]
  simp
@[simp] theorem inv_cup_distr : (f ⊔ g)# = f# ⊔ g# := by
  apply inc_antisym
  · rw[← inv_inc_move]
    apply inc_cup.mpr
    constructor
    · rw[inv_inc_move]
      apply cup_l
    · rw[inv_inc_move]
      apply cup_r
  · rw[← inc_inv, ← inv_inc_move]
    apply inc_cup.mpr
    simp

@[simp] theorem inv_cap_distr : (f ⊓ g)# = f# ⊓ g# := by
  apply inc_antisym
  · apply inc_cap.mpr
    constructor
    · rw[← inv_inc_move]
      simp
    · rw[← inv_inc_move]
      simp
  · rw[inv_inc_move]
    apply inc_cap.mpr
    constructor
    · rw[← inv_inc_move]
      simp
    · rw[← inv_inc_move]
      simp



@[simp] theorem rpc_inv_distr : (f ⇒ g)# = f# ⇒ g# := by
  apply inc_lower.mpr
  intro h
  apply Iff.intro
  · intro H
    rw[inc_rpc, inv_inc_move]
    simp
    rw[← inc_rpc, ← inv_inc_move]
    assumption
  · intro H
    rw[inv_inc_move, inc_rpc, ← inc_inv]
    simp
    rw[← inc_rpc]
    assumption

@[simp] theorem inv_empty : (φ X Y)# = φ Y X := by
  apply c.inc_antisym
  · rw[← inv_inc_move]
    simp
  · rw[← inc_inv, ← inv_inc_move]
    simp
@[simp] theorem inv_universal : (Δ X Y)# = Δ Y X := by
  apply c.inc_antisym
  · simp
  · rw[inv_inc_move]
    simp
@[simp] theorem inv_id (X:c.ob) : (idr X)# = idr X := by
  conv =>
    lhs
    rw[← comp_id_l (idr X #)]
    conv =>
      lhs
      rw[← inv_invol (idr X)]
  rw[← comp_inv, ← inv_move]
  simp

@[simp] theorem comp_cup_distr_l (f:c.rel X Y) (g g':c.rel Y Z) :
  f ∘ (g ⊔ g') = (f ∘ g) ⊔ (f ∘ g') := by
  apply inc_upper.mpr
  intro h
  apply Iff.intro
  · intro H
    apply c.inc_cup.mpr
    constructor
    all_goals
      apply inc_trans _ H
      apply comp_inc_compat_ab_ab'
      simp
  · intro H
    rw [← inv_invol f, ← inc_redidual]
    apply inc_cup.mpr
    constructor
    all_goals
      rw[inc_redidual]
      apply inc_trans _ H
      simp
@[simp] theorem comp_cup_distr_r (f f':c.rel X Y) (g:c.rel Y Z) :
  (f ⊔ f') ∘ g = (f ∘ g) ⊔ (f' ∘ g) := by
  rw[← inv_invol f, ← inv_invol f', ← inv_invol g, ← inv_cup_distr, ← comp_inv, comp_cup_distr_l]
  simp
@[simp] theorem comp_cap_distr (f:c.rel X Y) (g g':c.rel Y Z)(h:c.rel Z W) :
  (f ∘ (g ⊓ g')) ∘ h ⊑ ((f ∘ g) ∘ h) ⊓ (f ∘ g') ∘ h := by
  apply inc_cap.mpr
  constructor
  all_goals
    rw[← comp_assoc, ← comp_assoc]
    apply comp_inc_compat_ab_ab'
    apply comp_inc_compat_ab_a'b
    simp
@[simp] theorem comp_cap_distr_l (f:c.rel X Y) (g g':c.rel Y Z) :
  f ∘ (g ⊓ g') ⊑ (f ∘ g) ⊓ (f ∘ g') := by
  have H := comp_cap_distr f g g' (idr Z)
  simp at H
  assumption
@[simp] theorem comp_cap_distr_r (f f':c.rel X Y) (g:c.rel Y Z) :
  (f ⊓ f') ∘ g ⊑ (f ∘ g) ⊓ (f' ∘ g) := by
  have H := comp_cap_distr (idr X) f f' g
  simp at H
  assumption
@[simp] theorem comp_empty_r : f ∘ φ Y Z = φ X Z := by
  apply inc_antisym
  · rw[← inv_invol f, ← inc_redidual]
    simp
  · simp
@[simp] theorem comp_empty_l : φ X Y ∘ f = φ X Z := by
  rw[← inv_invol']
  simp
theorem comp_either_empty {f:c.rel X Y}{g:c.rel Y Z} :
  f = φ X Y ∨ g = φ Y Z → f ∘ g = φ X Z := by
  intro H
  cases H
  case inl H' =>
    rw[H']
    simp
  case inr H' =>
    rw[H']
    simp
theorem comp_neither_empty {f:c.rel X Y}{g:c.rel Y Z} :
  f ∘ g ≠ φ X Z → f ≠ φ X Y ∧ g ≠ φ Y Z := by
  intro H
  constructor
  all_goals
  · intro H'
    rw[H'] at H
    simp at H

theorem unit_identity_empty (I:unit_ob) : φ I.val I.val ≠ idr I.val := (c.unit_axioms I.property).left
theorem unit_identity_universal {I:unit_ob} : Δ I.val I.val = idr I.val := by
  rw[(c.unit_axioms I.property).right.left]
theorem unit_universal (I:unit_ob)(X:c.ob) :
  Δ X I.val ∘ Δ I.val X = Δ X X :=
  (c.unit_axioms I.property).right.right X
theorem unit_empty_universal (I:unit_ob) :
  φ I.val I.val ≠ Δ I.val I.val := by
  rw[unit_identity_universal]
  exact unit_identity_empty I



theorem empty_unit (I : unit_ob): φ X X = Δ X X ↔ φ X I.val = Δ X I.val  := by
  apply Iff.intro
  · intro H
    apply inc_antisym
    · simp
    · conv =>
        rhs
        rw[← @comp_empty_l _ _ _ _ (Δ X I.val)]
      conv =>
        lhs
        rw[← comp_id_l (Δ X I.val)]
      apply comp_inc_compat_ab_a'b
      rw[H]
      simp
  · intro H
    rw[← unit_universal I, ← H]
    simp
theorem unit_empty (I : unit_ob): φ X X = Δ X X ↔ φ I.val X = Δ I.val X  := by
  apply Iff.intro
  · intro H
    apply inc_antisym
    · simp
    · conv =>
        rhs
        rw[← @comp_empty_r _ _ _ _ (Δ I.val X)]
      conv =>
        lhs
        rw[← comp_id_r (Δ I.val X)]
      apply comp_inc_compat_ab_ab'
      rw[H]
      simp
  · intro H
    rw[← unit_universal I, ← H]
    simp
theorem tarski1 (I:unit_ob){f:c.rel X Y} : f ≠ φ X Y →
  (Δ I.val X ∘ f) ∘ Δ Y I.val ≠ φ I.val I.val := by
  intro H H'
  apply H
  apply inc_antisym
  · have H0 : f ⊑ (Δ X X ∘ f) ∘ Δ Y Y := by
      conv => lhs; rw[← comp_id_r f]
      apply comp_inc_compat
      · conv => lhs ; rw[← comp_id_l f]
        apply comp_inc_compat_ab_a'b
        simp
      · simp
    apply inc_trans H0
    rw[← unit_universal I, ← unit_universal I, comp_assoc]
    conv => lhs; conv => lhs; rw[← comp_assoc, ← comp_assoc]; conv => rhs; rw[comp_assoc, H']
    simp
  · simp
theorem tarski2 (I:unit_ob)(X Y:c.ob) :
  Δ X I.val ∘ Δ I.val Y = Δ X Y := by
  apply c.inc_antisym
  · simp
  · have H : (Δ X I.val ∘ Δ I.val X) ∘ Δ X Y ⊑ Δ X I.val ∘ Δ I.val Y := by
      rw[← comp_assoc]
      apply comp_inc_compat_ab_ab'
      simp
    apply inc_trans _ H
    · rw[unit_universal I X]
      apply comp_inc_compat_b_ab
      simp

-- theorem tarski {I:unit_ob}(f:c.rel X Y): (Δ X X ∘ f) ∘ Δ Y Y = Δ X Y := by
--   rw[← unit_universal , ← unit_universal, ← comp_assoc, ← comp_assoc]
--   conv => lhs; conv => rhs; rw[comp_assoc, comp_assoc] ; +
--   rw[tarski2 (⟨X, c.is_unit X⟩ : unit_ob) X Y]
--   rw[tarski2 (⟨Y, c.is_unit Y⟩ : unit_ob) X Y]
--   simp






end Dedekind
section Shroder
variable [c : Shroder]
variable {X Y Z: c.ob}
end Shroder

section sum
variable [c : Dedekind]
variable {X Y Z: c.ob}
def sum_ob (X Y:c.ob) := {S : c.ob // ∃ (l : c.rel X S) (r : c.rel Y S),
      l ∘ l# = idr X ∧ r ∘ r# = idr Y ∧ l ∘ r# = φ X Y ∧ (l# ∘ l) ⊔ (r# ∘ r) = idr S}
infixl:120 " ⊕ " => sum_ob.val

def inl {X Y:c.ob}(S:sum_ob X Y) : c.rel X S.val := (S.property.some)
end sum

-- theorem comp_not_empty_universal (f:c.rel X Y) :
--   f ≠ φ X Y → f ∘ Δ Y Z ≠ φ X Z := by
--   intro H H0
--   rw[← comp_empty_r] at H0

theorem comp_unit_universal (I:unit_ob): Δ X I.val ∘ Δ I.val Y = Δ X Y := by
  apply c.inc_antisym
  · simp
  ·
  apply comp_inc_compat_ab_ab'
  apply comp_inc_compat_ab_a'b
  simp
theorem talski1 (I:unit_ob) (f:c.rel X Y) :
  f ≠ φ X Y → (Δ I.val X ∘ f) ∘ Δ Y I.val = Δ I.val I.val := by
  intro H
  have H' : Δ I.val X ≠ φ I.val X := by
    intro H''
    have H''' := unit_universal I X
    rw[H''] at H'''
    simp at H'''
    have H0 := rel_unique H'''
    rw[H''] at H
    rw[← comp_empty_r] at H
    exact H
  apply c.inc_antisym
  · simp
  · rw[← comp_assoc, ← comp_assoc]
    apply comp_inc_compat_ab_ab'
    apply comp_inc_compat_ab_a'b
    simp



theorem unit_empty_or_universal {I:unit_ob} (f:c.rel I.val I.val) :
  (f = φ I.val I.val) ∨ (f = Δ I.val I.val) := by

  f ⊑ idr I.val
    apply inc_antisym
    · exact H.left
    · exact H.right
  · left
    classical.not_and_or H
    push_neg at H
    cases H
    case inl H' =>
      left
      apply inc_antisym
      · exact H'
      · exact inc_universal f
    case inr H' =>
      right
      apply inc_antisym
      · exact inc_universal f
      · exact H'
end Unitarity
section automaton
variable [c : Dedekind]
variable {X Y Z: c.ob}
structure NFA (I:unit_ob)(S : Type)(Q : c.ob) where
  β : c.rel I.val Q  -- start state (could be `Set Q` equivalently)
  τ : c.rel Q I.val  -- accepting predicate (could be `Set Q` equivalently)
  δ : S → c.rel Q Q  -- transition relation (could be `Q → Set Q` equivalently)

def dstar [c : Dedekind]{I:unit_ob}{S : Type}{Q : c.ob}(M:NFA I S Q) : (List S) → c.rel Q Q
  | [] => idr Q
  | (a::as) => M.δ a ∘ dstar M as
def accept {I:unit_ob}{S : Type}{Q:c.ob}(M:NFA I S Q)(w : List S) : Prop :=
  (M.β ∘ dstar M w) ∘ M.τ = idr I.val

theorem cup_nfa {I:unit_ob}{S : Type}{Q Q':c.ob}(M:NFA I S Q)(M':NFA I S Q')(w : List S) :
  accept M w ∨ accept M' w → ∃ (Q'':c.ob)(M'':NFA I S Q''), accept M'' w := by
  intro H
  cases H
  case inl H' =>
    rw[accept, dstar, List.append]
    rw[H']
    simp
    rw[comp_id_r]
    simp
  case inr H' =>
    rw[accept, dstar, List.append]
    rw[H']
    simp
    rw[comp_id_r]
    simp
