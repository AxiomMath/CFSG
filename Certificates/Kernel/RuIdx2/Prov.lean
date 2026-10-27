module

public import Certificates.Kernel.RuIdx2.GlueX
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoRuPT

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2.Prov

open CFSG.KD.RuIdx2 CFSG.KD.RuIdx2.Sem CFSG.KD.RuIdx2.Lab CFSG.KC.RuIdx2
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Quasithin.H13.K1262Two.RuP
open CFSG.Sporadic.Ru.Native (ruData)

section Group

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 4060)] (a b : Γ)

theorem lt_two : lt a b 2 = ruT1 a b := (Ru4120.H.slpElts_ruProg a b (by decide)).symm

theorem lt_three : lt a b 3 = ruT2 a b := (Ru4120.H.slpElts_ruProg a b (by decide)).symm

theorem lt_four : lt a b 4 = ruT3 a b := (Ru4120.H.slpElts_ruProg a b (by decide)).symm

theorem RS_eq {u : Nat} {Ls : List (List Nat)}
    (hn : (List.range (nr u)).map (fun l => unW (RG u l)) = Ls) :
    RS a b u = Ls.map fun L => (L.map (lt a b)).prod := by
  unfold RS wE
  rw [← hn, List.map_map]
  rfl

theorem Rv_100 : Rv a b 0 = Subgroup.closure {x | x ∈ [ruT2 a b, ruT1 a b * ruT2 a b * ruT1 a b,
    ruT3 a b, ruT1 a b * ruT3 a b * ruT1 a b]} := by
  unfold Rv
  rw [RS_eq a b (u := 0) (Ls := [[3], [2, 3, 2], [4], [2, 4, 2]]) (by decide +kernel)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, lt_two, lt_three,
    lt_four, mul_assoc]

theorem Rv_010 : Rv a b 1 = Subgroup.closure {x | x ∈ [ruT1 a b, ruT2 a b * ruT1 a b * ruT2 a b,
    ruT3 a b, ruT2 a b * ruT3 a b * ruT2 a b]} := by
  unfold Rv
  rw [RS_eq a b (u := 1) (Ls := [[2], [3, 2, 3], [4], [3, 4, 3]]) (by decide +kernel)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, lt_two, lt_three,
    lt_four, mul_assoc]

theorem Rv_001 : Rv a b 2 = Subgroup.closure {x | x ∈ [ruT1 a b, ruT3 a b * ruT1 a b * ruT3 a b,
    ruT2 a b, ruT3 a b * ruT2 a b * ruT3 a b]} := by
  unfold Rv
  rw [RS_eq a b (u := 2) (Ls := [[2], [4, 2, 4], [3], [4, 3, 4]]) (by decide +kernel)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, lt_two, lt_three,
    lt_four, mul_assoc]

theorem Rv_110 : Rv a b 3 = Subgroup.closure {x | x ∈ [ruT2 a b * ruT1 a b, ruT3 a b,
    ruT1 a b * ruT3 a b * ruT1 a b]} := by
  unfold Rv
  rw [RS_eq a b (u := 3) (Ls := [[3, 2], [4], [2, 4, 2]]) (by decide +kernel)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, lt_two, lt_three,
    lt_four, mul_assoc]

theorem Rv_101 : Rv a b 4 = Subgroup.closure {x | x ∈ [ruT2 a b, ruT1 a b * ruT2 a b * ruT1 a b,
    ruT3 a b * ruT1 a b]} := by
  unfold Rv
  rw [RS_eq a b (u := 4) (Ls := [[3], [2, 3, 2], [4, 2]]) (by decide +kernel)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, lt_two, lt_three,
    lt_four, mul_assoc]

theorem Rv_011 : Rv a b 5 = Subgroup.closure {x | x ∈ [ruT1 a b, ruT2 a b * ruT1 a b * ruT2 a b,
    ruT3 a b * ruT2 a b]} := by
  unfold Rv
  rw [RS_eq a b (u := 5) (Ls := [[2], [3, 2, 3], [4, 3]]) (by decide +kernel)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, lt_two, lt_three,
    lt_four, mul_assoc]

theorem Rv_111 : Rv a b 6 = Subgroup.closure {x | x ∈ [ruT2 a b * ruT1 a b,
    ruT3 a b * ruT1 a b]} := by
  unfold Rv
  rw [RS_eq a b (u := 6) (Ls := [[3, 2], [4, 2]]) (by decide +kernel)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, lt_two, lt_three,
    lt_four, mul_assoc]

end Group

attribute [local instance] GlueX.act4060


theorem noBig_100 : NoBig (Subgroup.closure {x | x ∈ [ruT2 (a ruData) (b ruData),
    ruT1 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData),
    ruT3 (a ruData) (b ruData),
    ruT1 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData)]}) := by
  have h := GlueX.noBig_two (u := 0) (by norm_num) (by norm_num)
  rwa [Rv_100] at h

theorem noBig_010 : NoBig (Subgroup.closure {x | x ∈ [ruT1 (a ruData) (b ruData),
    ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData),
    ruT3 (a ruData) (b ruData),
    ruT2 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData)]}) := by
  have h := GlueX.noBig_two (u := 1) (by norm_num) (by norm_num)
  rwa [Rv_010] at h

theorem noBig_001 : NoBig (Subgroup.closure {x | x ∈ [ruT1 (a ruData) (b ruData),
    ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData),
    ruT2 (a ruData) (b ruData),
    ruT3 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData)]}) := by
  have h := GlueX.noBig_001
  rwa [Rv_001] at h

theorem noBig_110 : NoBig (Subgroup.closure {x | x ∈ [
    ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData), ruT3 (a ruData) (b ruData),
    ruT1 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData)]}) := by
  have h := GlueX.noBig_two (u := 3) (by norm_num) (by norm_num)
  rwa [Rv_110] at h

theorem noBig_101 : NoBig (Subgroup.closure {x | x ∈ [ruT2 (a ruData) (b ruData),
    ruT1 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData),
    ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData)]}) := by
  have h := GlueX.noBig_two (u := 4) (by norm_num) (by norm_num)
  rwa [Rv_101] at h

theorem noBig_011 : NoBig (Subgroup.closure {x | x ∈ [ruT1 (a ruData) (b ruData),
    ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData),
    ruT3 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData)]}) := by
  have h := GlueX.noBig_two (u := 5) (by norm_num) (by norm_num)
  rwa [Rv_011] at h

theorem noBig_111 : NoBig (Subgroup.closure {x | x ∈ [
    ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData),
    ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData)]}) := by
  have h := GlueX.noBig_two (u := 6) (by norm_num) (by norm_num)
  rwa [Rv_111] at h

end CFSG.KD.RuIdx2.Prov

end
