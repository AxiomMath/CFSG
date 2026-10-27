
module

public import Certificates.Kernel.J4Count.FiveM24Base

public import Certificates.Kernel.J4Count.StarsBase2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelJ4Count.Five

open CFSG.KC.J4Five CFSG.KC.J4Q CFSG.KC.J4Count CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Sporadic.J4.QT2 CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs Equiv Subgroup

section Stars

end Stars

section Hom

theorem card_centralizer_Hj_le' {c : J} (hcH : c ∈ Hj) {n m : ℕ}
    (hE : Nat.card ↥(centralizer ({c} : Set J) ⊓ Eg uJ 11) ≤ n)
    (hG : Nat.card ↥(G24 ⊓ centralizer ({Stars.starHom ⟨c, hcH⟩} : Set (Perm (Fin 24)))) ≤ m) :
    Nat.card ↥(centralizer ({c} : Set J) ⊓ Hj) ≤ m * n := by
  set c' : ↥Hj := ⟨c, hcH⟩ with hc'
  let D : Subgroup ↥Hj := centralizer ({c'} : Set ↥Hj)
  have hD : Nat.card ↥(centralizer ({c} : Set J) ⊓ Hj) = Nat.card ↥D := by
    have hmap : D.map Hj.subtype = centralizer ({c} : Set J) ⊓ Hj := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨centJ_iff.2 (coe_comm' ((mem_cent_iff' (G := ↥Hj)).1 hy)).symm, y.2⟩
      · rintro ⟨hx, hxH⟩
        refine ⟨⟨x, hxH⟩, (mem_cent_iff' (G := ↥Hj)).2 (Subtype.ext ?_), rfl⟩
        exact (centJ_iff.1 hx).symm
    rw [← hmap]
    exact (Nat.card_congr (D.equivMapOfInjective Hj.subtype Hj.subtype_injective).toEquiv).symm
  let φ : ↥D →* Perm (Fin 24) := Stars.starHom.comp D.subtype
  have hmul : Nat.card ↥D = Nat.card (↥D ⧸ φ.ker) * Nat.card φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hquot : Nat.card (↥D ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hrange : Nat.card φ.range ≤ m := by
    refine le_trans (Subgroup.card_le_of_le
      (K := G24 ⊓ centralizer ({Stars.starHom c'} : Set (Perm (Fin 24)))) ?_) hG
    rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← range_eq]
      exact ⟨x.1, rfl⟩
    · have hx : (x : ↥Hj) * c' = c' * (x : ↥Hj) := (mem_cent_iff' (G := ↥Hj)).1 x.2
      have := congrArg Stars.starHom hx
      rw [map_mul, map_mul] at this
      exact (mem_cent_iff' (G := Perm (Fin 24))).2 this
  have hker : Nat.card φ.ker ≤ n := by
    have hmem : ∀ k : φ.ker, (((k.1 : ↥D) : ↥Hj) : J) ∈ centralizer ({c} : Set J) ⊓ Eg uJ 11 := by
      intro k
      refine ⟨?_, ?_⟩
      · have hx : ((k.1 : ↥D) : ↥Hj) * c' = c' * ((k.1 : ↥D) : ↥Hj) :=
          (mem_cent_iff' (G := ↥Hj)).1 k.1.2
        exact centJ_iff.2 (coe_comm' hx).symm
      · have hk : Stars.starHom ((k.1 : ↥D) : ↥Hj) = 1 := k.2
        have : ((k.1 : ↥D) : ↥Hj) ∈ Stars.starHom.ker := hk
        rw [Stars.ker_starHom, Subgroup.mem_subgroupOf] at this
        exact this
    refine le_trans (Nat.card_le_card_of_injective
      (fun k : φ.ker => (⟨(((k.1 : ↥D) : ↥Hj) : J), hmem k⟩ :
        ↥(centralizer ({c} : Set J) ⊓ Eg uJ 11))) ?_) hE
    intro k₁ k₂ h
    have h1 := congrArg Subtype.val h
    simp only at h1
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  rw [hD, hmul, hquot]
  exact Nat.mul_le_mul hrange hker

theorem card_centralizer_fiveElt_Hj_le :
    Nat.card ↥(Subgroup.centralizer ({fiveElt} : Set J) ⊓ Hj) ≤ 480 :=
  card_centralizer_Hj_le' (m := 60) (n := 8) fiveElt_mem_Hj
    (card_centralizer_inf_Eg_fiveElt CertificateChecks.KernelJ4Q.matFacts).le card_cent_xiBar

end Hom

end CertificateChecks.KernelJ4Count.Five

end
