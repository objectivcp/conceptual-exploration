import Order2.Basic

/-! The rules of the reduced basis in order2_vampire_etp/exploration.log, from Vampire's proofs. -/

/-- Rule 1 of the reduced basis. -/
theorem Equation39_43_implies_Equation41 (G : Type _) [Magma G] (h1 : Equation39 G) (h2 : Equation43 G) : Equation41 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := mod_symm (h2 ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK2) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq7 eq7 -- superposition 7,7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq8 eq7 -- superposition 7,8
  have eq32 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK2) := superpose eq10 eq9 -- superposition 9,10
  have eq39 (X0 X1 : G) : (X0 ◇ sK0) ≠ (X1 ◇ sK2) := superpose eq10 eq32 -- superposition 32,10
  have eq62 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ X1) := superpose eq14 eq10 -- superposition 10,14
  have eq77 (X0 X1 : G) : (X0 ◇ X0) ≠ (X1 ◇ sK0) := superpose eq14 eq39 -- superposition 39,14
  subsumption eq77 eq62

/-- Rule 2 of the reduced basis. -/
theorem Equation39_40_implies_Equation41 (G : Type _) [Magma G] (h1 : Equation39 G) (h2 : Equation40 G) : Equation41 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h2 ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK2) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq7 eq7 -- superposition 7,7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ X1) := superpose eq8 eq7 -- superposition 7,8
  have eq36 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK2) := superpose eq10 eq9 -- superposition 9,10
  subsumption eq36 eq18

/-- Rule 3 of the reduced basis. -/
theorem Equation38_39_implies_Equation41 (G : Type _) [Magma G] (h1 : Equation38 G) (h2 : Equation39 G) : Equation41 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h2 ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK2) := mod_symm nh
  have eq11 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq7 eq9 -- superposition 9,7
  have eq12 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq7 eq11 -- superposition 11,7
  have eq18 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq8 eq7 -- superposition 7,8
  have eq21 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq8 eq12 -- superposition 12,8
  subsumption eq21 eq18

/-- Rule 4 of the reduced basis. -/
theorem Equation23_43_implies_Equation8 (G : Type _) [Magma G] (h1 : Equation23 G) (h2 : Equation43 G) : Equation8 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq7 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h2 ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq7 -- forward demodulation 7,8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10
  subsumption eq11 rfl

/-- Rule 5 of the reduced basis. -/
theorem Equation23_40_implies_Equation31 (G : Type _) [Magma G] (h1 : Equation23 G) (h2 : Equation40 G) : Equation31 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h2 ..)
  have eq9 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq16 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq8 eq9 -- superposition 9,8
  have eq17 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq8 eq7 -- superposition 7,8
  subsumption eq16 eq17

/-- Rule 6 of the reduced basis. -/
theorem Equation23_39_implies_Equation5 (G : Type _) [Magma G] (h1 : Equation23 G) (h2 : Equation39 G) : Equation5 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := mod_symm (h2 ..)
  have eq9 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq7 -- forward demodulation 7,8
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq8 eq9 -- superposition 9,8
  subsumption eq14 eq10

/-- Rule 7 of the reduced basis. -/
theorem Equation23_38_implies_Equation24 (G : Type _) [Magma G] (h1 : Equation23 G) (h2 : Equation38 G) : Equation24 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := mod_symm (h2 ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq8 eq8 -- superposition 8,8
  have eq11 (X0 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq8 eq9 -- superposition 9,8
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq8 eq7 -- superposition 7,8
  have eq36 (X0 X1 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ X1) := superpose eq10 eq11 -- superposition 11,10
  have eq56 : sK0 ≠ sK0 := superpose eq12 eq36 -- superposition 36,12
  subsumption eq56 rfl

/-- Rule 8 of the reduced basis. -/
theorem Equation26_31_implies_Equation40 (G : Type _) [Magma G] (h1 : Equation26 G) (h2 : Equation31 G) : Equation40 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := mod_symm (h2 ..)
  have eq9 : (sK1 ◇ sK1) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq8 eq7 -- superposition 7,8
  have eq22 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11
  subsumption eq22 eq11

/-- Rule 9 of the reduced basis. -/
theorem Equation25_26_implies_Equation24 (G : Type _) [Magma G] (h1 : Equation25 G) (h2 : Equation26 G) : Equation24 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq7 eq8 -- superposition 8,7
  have eq16 (X0 : G) : sK0 ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq11 eq9 -- superposition 9,11
  have eq21 : sK0 ≠ sK0 := superpose eq8 eq16 -- superposition 16,8
  subsumption eq21 rfl

/-- Rule 10 of the reduced basis. -/
theorem Equation31_43_implies_Equation11 (G : Type _) [Magma G] (h1 : Equation31 G) (h2 : Equation43 G) : Equation11 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h2 ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq8 eq7 -- superposition 7,8
  have eq24 : sK0 ≠ sK0 := superpose eq14 eq9 -- superposition 9,14
  subsumption eq24 rfl

/-- Rule 11 of the reduced basis. -/
theorem Equation26_43_implies_Equation29 (G : Type _) [Magma G] (h1 : Equation26 G) (h2 : Equation43 G) : Equation29 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h2 ..)
  have eq9 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq8 eq7 -- forward demodulation 7,8
  have eq14 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq8 eq9 -- superposition 9,8
  have eq15 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq8 eq14 -- forward demodulation 14,8
  subsumption eq15 eq10

/-- Rule 12 of the reduced basis. -/
theorem Equation25_8_implies_Equation3 (G : Type _) [Magma G] (h1 : Equation25 G) (h2 : Equation8 G) : Equation3 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq7 -- superposition 7,8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11
  subsumption eq12 rfl

/-- Rule 13 of the reduced basis. -/
theorem Equation16_26_implies_Equation29 (G : Type _) [Magma G] (h1 : Equation16 G) (h2 : Equation26 G) : Equation29 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq8 eq7 -- superposition 7,8
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11
  subsumption eq20 rfl

/-- Rule 14 of the reduced basis. -/
theorem Equation29_43_implies_Equation26 (G : Type _) [Magma G] (h1 : Equation29 G) (h2 : Equation43 G) : Equation26 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := mod_symm (h2 ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq8 eq7 -- forward demodulation 7,8
  have eq12 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq8 eq9 -- superposition 9,8
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq8 eq10 -- superposition 10,8
  have eq19 : sK0 ≠ sK0 := superpose eq14 eq12 -- superposition 12,14
  subsumption eq19 rfl

/-- Rule 15 of the reduced basis. -/
theorem Equation29_31_implies_Equation11 (G : Type _) [Magma G] (h1 : Equation29 G) (h2 : Equation31 G) : Equation11 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq8 eq7 -- superposition 7,8
  have eq26 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12
  subsumption eq26 rfl

/-- Rule 16 of the reduced basis. -/
theorem Equation26_29_implies_Equation43 (G : Type _) [Magma G] (h1 : Equation26 G) (h2 : Equation29 G) : Equation43 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h2 ..)
  have eq9 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq8 eq7 -- superposition 7,8
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq9 -- superposition 9,12
  subsumption eq33 rfl

/-- Rule 17 of the reduced basis. -/
theorem Equation11_31_implies_Equation40 (G : Type _) [Magma G] (h1 : Equation11 G) (h2 : Equation31 G) : Equation40 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := mod_symm (h2 ..)
  have eq9 : (sK1 ◇ sK1) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq8 eq7 -- superposition 7,8
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq15 eq9 -- superposition 9,15
  subsumption eq29 eq15

/-- Rule 18 of the reduced basis. -/
theorem Equation31_3_implies_Equation5 (G : Type _) [Magma G] (h1 : Equation31 G) (h2 : Equation3 G) : Equation5 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 : G) : (X0 ◇ X0) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq8 eq7 -- forward demodulation 7,8
  have eq11 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10
  subsumption eq11 rfl

/-- Rule 19 of the reduced basis. -/
theorem Equation28_43_implies_Equation2 (G : Type _) [Magma G] (h1 : Equation28 G) (h2 : Equation43 G) : Equation2 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := mod_symm (h2 ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq8 eq7 -- forward demodulation 7,8
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq10 eq10 -- superposition 10,10
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq14 -- forward demodulation 14,10
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq15 eq8 -- superposition 8,15
  have eq26 (X0 X1 : G) : X0 = X1 := superpose eq21 eq15 -- superposition 15,21
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq9 -- superposition 9,26
  subsumption eq48 eq26

/-- Rule 20 of the reduced basis. -/
theorem Equation26_28_implies_Equation2 (G : Type _) [Magma G] (h1 : Equation26 G) (h2 : Equation28 G) : Equation2 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq8 eq7 -- superposition 7,8
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq9 -- superposition 9,13
  subsumption eq20 eq13

/-- Rule 21 of the reduced basis. -/
theorem Equation25_43_implies_Equation2 (G : Type _) [Magma G] (h1 : Equation25 G) (h2 : Equation43 G) : Equation2 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h2 ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq8 eq7 -- forward demodulation 7,8
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq8 eq10 -- superposition 10,8
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq10 eq12 -- superposition 12,10
  have eq18 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq18 -- forward demodulation 18,8
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq17 -- forward demodulation 17,8
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq21 -- forward demodulation 21,12
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq10 eq22 -- forward demodulation 22,10
  have eq38 (X0 X1 : G) : X0 = X1 := superpose eq24 eq23 -- superposition 23,24
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq9 -- superposition 9,38
  subsumption eq53 eq38

/-- Rule 22 of the reduced basis. -/
theorem Equation16_25_implies_Equation5 (G : Type _) [Magma G] (h1 : Equation16 G) (h2 : Equation25 G) : Equation5 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq8 -- superposition 8,7
  have eq15 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10
  subsumption eq15 rfl

/-- Rule 23 of the reduced basis. -/
theorem Equation28_29_implies_Equation2 (G : Type _) [Magma G] (h1 : Equation28 G) (h2 : Equation29 G) : Equation2 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq8 eq7 -- superposition 7,8
  have eq21 (X0 X1 : G) : X0 = X1 := superpose eq15 eq8 -- superposition 8,15
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq9 -- superposition 9,21
  subsumption eq38 eq21

/-- Rule 24 of the reduced basis. -/
theorem Equation25_29_implies_Equation2 (G : Type _) [Magma G] (h1 : Equation25 G) (h2 : Equation29 G) : Equation2 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq8 eq7 -- superposition 7,8
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq9 -- superposition 9,14
  subsumption eq21 eq14

/-- Rule 25 of the reduced basis. -/
theorem Equation10_28_implies_Equation5 (G : Type _) [Magma G] (h1 : Equation10 G) (h2 : Equation28 G) : Equation5 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq7 -- superposition 7,7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11
  subsumption eq13 rfl

/-- Rule 26 of the reduced basis. -/
theorem Equation28_9_implies_Equation2 (G : Type _) [Magma G] (h1 : Equation28 G) (h2 : Equation9 G) : Equation2 G := by
  apply Classical.byContradiction
  intro nh
  simp only [Classical.not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := mod_symm (h1 ..)
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := mod_symm (h2 ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq8 -- superposition 8,7
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq7 -- superposition 7,8
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq8 eq15 -- forward demodulation 15,8
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq12 -- forward demodulation 12,7
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq17 eq16 -- superposition 16,17
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq9 -- superposition 9,24
  subsumption eq36 eq24
