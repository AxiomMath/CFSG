
module

public import Certificates.Kernel.SpinOrb.Checks
public import CFSG.Certificates.Kernel.SpinOrbKSound
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.GLS.Bg.TwoGroups.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.TwoThin.G.Section
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.GH74.KGroups.L28Tables
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverGH
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternal
public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassPoint
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.McL
public import CFSG.Walter.J1Recog
public import Certificates.Certificate10025
public import Certificates.Certificate5007
public import Certificates.Certificate7233Base

public section

namespace CFSG.KD.SpinOrb

open CFSG.KC.SpinOrb CFSG.KC.LQT CFSG.Alternating.Multipliers.Spin
open CFSG.ComponentClassification.Sol76.Sig.GSYard02

#kc_forall_tree ch13004mat8 (fun j => matOK 16 gam8 (pairsS8.getD j ([], [])) (R8.getD j []) = true)
  4 CFSG.KD.SpinOrb.ch13004mat8_

#kc_forall_tree ch13004mat10
  (fun j => matOK 32 gam10 (pairsS10.getD j ([], [])) (R10.getD j []) = true)
  5 CFSG.KD.SpinOrb.ch13004mat10_

#kc_forall_tree ch13004orb8 (fun k => orbitK 16 128 R8 T8 S8 TR8 L8 SG8 k = true)
  128 CFSG.KD.SpinOrb.ch13004orb8_

#kc_forall_tree ch13004orb10 (fun k => orbitK 32 256 R10 T10 S10 TR10 L10 SG10 k = true)
  256 CFSG.KD.SpinOrb.ch13004orb10_

#kc_forall_tree ch13004psi8 (fun k => psiAt 8 64 PG8 PE8 PA8 PS8 PC8 k = true)
  64 CFSG.KD.SpinOrb.ch13004psi8_

#kc_forall_tree ch13004psi9 (fun k => psiAt 9 64 PG9 PE9 PA9 PS9 PC9 k = true)
  64 CFSG.KD.SpinOrb.ch13004psi9_

#kc_forall_tree ch13004psi10 (fun k => psiAt 10 128 PG10 PE10 PA10 PS10 PC10 k = true)
  128 CFSG.KD.SpinOrb.ch13004psi10_

#kc_forall_tree ch13004psi11 (fun k => psiAt 11 128 PG11 PE11 PA11 PS11 PC11 k = true)
  128 CFSG.KD.SpinOrb.ch13004psi11_

#kc_forall_tree ch13004klein10 (fun idx => kleinAt 256 L10 KL10 idx = true)
  149 CFSG.KD.SpinOrb.ch13004klein10_

#kc_forall_tree ch13004inv10 (fun i => invAt 256 L10 INV10 i = true)
  256 CFSG.KD.SpinOrb.ch13004inv10_

#kc_forall_tree ch13004pairs10 (fun a => pairsAt 256 L10 KL10 149 INV10 W10 a = true)
  59 CFSG.KD.SpinOrb.ch13004pairs10_

theorem words8 : allPairs pairsS8 (wordsOK 8) = true ∧ pairsS8.length = 4 ∧ R8.length = 4 := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 ch13004words8
  obtain ⟨h2, h3⟩ := P.andB_iff.1 h2
  exact ⟨h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem words10 :
    allPairs pairsS10 (wordsOK 10) = true ∧ pairsS10.length = 5 ∧ R10.length = 5 := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 ch13004words10
  obtain ⟨h2, h3⟩ := P.andB_iff.1 h2
  exact ⟨h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem gens4 : gensEq 8 pairsS8 PG8 = true ∧ gensEq 9 pairsS8 PG9 = true ∧
    gensEq 10 pairsS10 PG10 = true ∧ gensEq 11 pairsS10 PG11 = true := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 ch13004gens
  obtain ⟨h1, h3⟩ := P.andB_iff.1 h1
  obtain ⟨h2, h4⟩ := P.andB_iff.1 h2
  exact ⟨h1, h3, h2, h4⟩

theorem sylowE8 : SylowFourJoined (E 8) := by
  obtain ⟨hw, hlen, hRl⟩ := words8
  obtain ⟨habel, hA⟩ := P.andB_iff.1 ch13004abel8
  have hE : Nat.card (E (6 + 2)) = 2 ^ 7 * 315 := by
    rw [card_E (by norm_num)]
    norm_num [Nat.factorial]
  exact sylow_normal_of_checks (m := 6) (N := 16) (M := 16) (by norm_num) (by norm_num) gam8 gam8 8
    LinearMap.id Function.injective_id ch13004gam8 ch13004gam8 (fun _ _ _ => rfl) pairsS8 hw hw
    R8 (hRl.trans hlen.symm) (fun j hj => ch13004mat8 j (lt_of_lt_of_eq hj hlen)) 128 (by norm_num) T8 S8 TR8
    L8 SG8 ch13004orb8 PG8 64 PE8 PA8 PS8 PC8 (by norm_num) (by norm_num) gens4.1 ch13004psi8 A8
    (by rw [hlen]; exact habel) (Nat.eq_of_beq_eq_true hA) (by omega) 7 315 (by norm_num) hE
    (by norm_num)

theorem sylowE9 : SylowFourJoined (E 9) := by
  obtain ⟨hw, hlen, hRl⟩ := words8
  obtain ⟨habel, hA⟩ := P.andB_iff.1 ch13004abel8
  obtain ⟨hG9, hpre⟩ := P.andB_iff.1 ch13004gam9
  have hE : Nat.card (E (7 + 2)) = 2 ^ 7 * 2835 := by
    rw [card_E (by norm_num)]
    norm_num [Nat.factorial]
  exact sylow_normal_of_checks (m := 7) (N := 16) (M := 16) (by norm_num) (by norm_num) gam9 gam8 8
    LinearMap.id Function.injective_id hG9 ch13004gam8
    (fun k hk u => by rw [prefixK_sound hpre k hk]; rfl) pairsS8 hw ch13004words9
    R8 (hRl.trans hlen.symm) (fun j hj => ch13004mat8 j (lt_of_lt_of_eq hj hlen)) 128 (by norm_num) T8 S8 TR8
    L8 SG8 ch13004orb8 PG9 64 PE9 PA9 PS9 PC9 (by norm_num) (by norm_num) gens4.2.1 ch13004psi9
    A8 (by rw [hlen]; exact habel) (Nat.eq_of_beq_eq_true hA) (by omega) 7 2835 (by norm_num) hE
    (by norm_num)

theorem sylowE10 : SylowFourJoined (E 10) := by
  obtain ⟨hw, hlen, hRl⟩ := words10
  have hI : INV10.length = 59 := Nat.eq_of_beq_eq_true ch13004invLen10
  have hE : Nat.card (E (8 + 2)) = 2 ^ 8 * 14175 := by
    rw [card_E (by norm_num)]
    norm_num [Nat.factorial]
  exact sylow_klein_of_checks (m := 8) (N := 32) (M := 32) (by norm_num) (by norm_num) gam10 gam10
    10 LinearMap.id Function.injective_id ch13004gam10 ch13004gam10 (fun _ _ _ => rfl) pairsS10 hw
    hw R10 (hRl.trans hlen.symm) (fun j hj => ch13004mat10 j (lt_of_lt_of_eq hj hlen)) 256 (by norm_num) T10
    S10 TR10 L10 SG10 ch13004orb10 PG10 128 PE10 PA10 PS10 PC10 (by norm_num) (by norm_num)
    gens4.2.2.1 ch13004psi10 KL10 149 W10 INV10 ch13004klein10 ch13004inv10
    (fun a ha => ch13004pairs10 a (lt_of_lt_of_eq ha hI)) 8 14175 (by norm_num) hE (by norm_num)

theorem sylowE11 : SylowFourJoined (E 11) := by
  obtain ⟨hw, hlen, hRl⟩ := words10
  obtain ⟨hG11, hkron⟩ := P.andB_iff.1 ch13004gam11
  have hI : INV10.length = 59 := Nat.eq_of_beq_eq_true ch13004invLen10
  have hE : Nat.card (E (9 + 2)) = 2 ^ 8 * 155925 := by
    rw [card_E (by norm_num)]
    norm_num [Nat.factorial]
  exact sylow_klein_of_checks (m := 9) (N := 64) (M := 32) (by norm_num) (by norm_num) gam11 gam10
    10 emb emb_injective hG11 ch13004gam10 (fun k hk => kronIK_sound ch13004gam10 hkron k hk)
    pairsS10 hw ch13004words11 R10 (hRl.trans hlen.symm) (fun j hj => ch13004mat10 j (lt_of_lt_of_eq hj hlen))
    256 (by norm_num) T10 S10 TR10 L10 SG10 ch13004orb10 PG11 128 PE11 PA11 PS11 PC11
    (by norm_num) (by norm_num) gens4.2.2.2 ch13004psi11 KL10 149 W10 INV10 ch13004klein10
    ch13004inv10 (fun a ha => ch13004pairs10 a (lt_of_lt_of_eq ha hI)) 8 155925 (by norm_num) hE
    (by norm_num)

end CFSG.KD.SpinOrb
