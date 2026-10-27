module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYA5S5Data

public section

namespace CertificateChecks.KernelHSStd

open CFSG.EvenSporadicStandard.HSStd.FiveY

abbrev A5 : Type := ↥(alternatingGroup (Fin 5))

@[expose] def cA (a : A5) : ℕ := (Finset.univ.filter fun g : A5 => g * a = a * g).card

@[expose] def cS (b : Equiv.Perm (Fin 5)) : ℕ :=
  (Finset.univ.filter fun g : Equiv.Perm (Fin 5) => g * b = b * g).card

theorem cardCent_eq (t : A5S5) : cardCent t = cA t.1 * cS t.2 := by
  have : (Finset.univ.filter fun g : A5S5 => g * t = t * g) =
      (Finset.univ.filter fun g : A5 => g * t.1 = t.1 * g) ×ˢ
        (Finset.univ.filter fun g : Equiv.Perm (Fin 5) => g * t.2 = t.2 * g) := by
    ext g
    simp [Prod.ext_iff]
  rw [cardCent, this, Finset.card_product, cA, cS]

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
theorem compCheck :
    ∀ a : A5, a * a = 1 → ∀ b : Equiv.Perm (Fin 5), b * b = 1 → cA a * cS b = 480 →
      (b = 1 ∧ ∀ x : A5, x * a = a * x → ∀ y : A5, y * a = a * y → x * y = y * x) ∨
      (a = 1 ∧ (∀ z : A5, (∀ g : A5, z * g = g * z) → z = 1) ∧
        ∀ z : Equiv.Perm (Fin 5), (∀ g : Equiv.Perm (Fin 5), g * b = b * g → z * g = g * z) →
          z = 1 ∨ z = b) := by
  decide +kernel

theorem a5s5Stmt_kernel : a5s5Stmt := by
  intro t ht2 ht1 hcard hz u hu2 hut hw hc
  rcases t with ⟨a, b⟩
  obtain ⟨z, hz1, hzt, -, hzall⟩ := hz
  obtain ⟨w, hwt, huw⟩ := hw
  obtain ⟨c, hc⟩ := hc
  rw [cardCent_eq] at hcard
  have ha : a * a = 1 := congrArg Prod.fst ht2
  have hb : b * b = 1 := congrArg Prod.snd ht2
  rcases compCheck a ha b hb hcard with ⟨rfl, hab⟩ | ⟨rfl, hA, hS⟩
  ·
    have hu2' : u.2 = 1 := by
      have e : c * u.2 * c⁻¹ = 1 := by simpa using hc
      have := congrArg (fun x => c⁻¹ * x * c) e
      simpa [mul_assoc] using this
    apply huw
    have hu1 : u.1 * a = a * u.1 := by
      have := congrArg Prod.fst hut
      simpa using this
    have hw1 : w.1 * a = a * w.1 := by
      have := congrArg Prod.fst hwt
      simpa using this
    refine Prod.ext ?_ ?_
    · exact hab u.1 hu1 w.1 hw1
    · simp [hu2']
  ·
    have h1 : z.1 = 1 := hA z.1 fun g => by
      have := congrArg Prod.fst (hzall (g, 1) (by simp))
      simpa using this
    have h2 : z.2 = 1 ∨ z.2 = b := hS z.2 fun g hg => by
      have := congrArg Prod.snd (hzall (1, g) (by simp [Prod.ext_iff, hg]))
      simpa using this
    rcases h2 with h2 | h2
    · exact hz1 (Prod.ext h1 h2)
    · exact hzt (Prod.ext h1 h2)

end CertificateChecks.KernelHSStd
