module

public import MacMahon.Rotations

@[expose] public section
namespace MacMahon

abbrev NonzeroColour := {c : Fin 7 // c ≠ 0}
def colourEquiv : Fin 6 ≃ NonzeroColour where
  toFun i := ⟨i.succ, i.succ_ne_zero⟩
  invFun c := c.val.pred c.property
  left_inv i := Fin.pred_succ i
  right_inv c := Subtype.ext (Fin.succ_pred c.val c.property)

/-- Arbitrary assignments using each of the six colours exactly once. -/
abbrev Colouring := Fin 6 ≃ NonzeroColour
abbrev Variety := {p : Pair // p.1 ≠ p.2}

noncomputable def orientedColouring (p : Variety × Fin 24) : Colouring :=
  Equiv.ofBijective
    (fun f => ⟨faceColours p.1.val.1 p.1.val.2 (rotations p.2 f),
      (face_colours_valid _ _ p.1.property).2 _⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro f g h
      exact (rotations_bijective p.2).1
        ((face_colours_valid _ _ p.1.property).1 (congrArg Subtype.val h)),
      Fintype.card_congr colourEquiv⟩)

lemma orientedColouring_injective : Function.Injective orientedColouring := by
  rintro ⟨⟨⟨i,j⟩,hij⟩,r⟩ ⟨⟨⟨u,v⟩,huv⟩,s⟩ heq
  have hf : ∀ f : Fin 6, faceColours i j (rotations r f) =
      faceColours u v (rotations s f) :=
    fun f => congrArg (fun e : Colouring => (e f).val) heq
  obtain ⟨si,hsi⟩ := rotation_inverse s
  obtain ⟨t,ht⟩ := rotation_composition r si
  have hvar : i = u ∧ j = v := varieties_distinct i j hij u v huv t (by
    intro f
    rw [ht f]
    have hh := hf (rotations si f)
    rwa [hsi f] at hh)
  obtain ⟨rfl,rfl⟩ := hvar
  have hrs : r = s := rotations_distinct (funext (fun f =>
    (face_colours_valid _ _ hij).1 (hf f)))
  subst s
  rfl

lemma card_variety : Fintype.card Variety = 30 := by decide +kernel
lemma card_colourings : Fintype.card Colouring = 720 := by
  rw [Fintype.card_equiv colourEquiv]
  norm_num

/-- Every six-colour face assignment has a unique labelled variety and rotation. -/
theorem all_colourings : Function.Bijective orientedColouring := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨orientedColouring_injective, ?_⟩
  rw [Fintype.card_prod, card_variety, Fintype.card_fin, card_colourings]

end MacMahon
