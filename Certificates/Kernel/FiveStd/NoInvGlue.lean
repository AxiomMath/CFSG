module

public import Certificates.Kernel.FiveStd.NGlue
public import Certificates.Kernel.FiveStd.ExpChk
public import CFSG.Certificates.Kernel.FiveStdKExpSound
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.LU.Local.FiveModelLeaf
public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

local instance instFact5 : Fact (Nat.Prime 5) := fact5

local notation "ιF" => Mat.ιF (ZMod 5)

theorem hM5 : Model ιF := Mat.model_ιF (F := ZMod 5)

theorem hK5 : Nat.card (vSub hM5) = 28800 := by
  have hgen := (clsOK_spec (clsF_eq 0 ▸ cls_ok 0 (by norm_num))).1
  exact card_vSub hM5 (fun l => decE (f20 G l))
    (fun l hl => ⟨valid_decE (hgen l hl).1, codeE_decE (validK_lt (hgen l hl).1)⟩) tree_all

theorem pow_eq_one_of_code {x : E} (hx : validE x = true) {n : Nat} (h : powK (codeE x) n = oneK) :
    ιF x ^ n = 1 := by
  rw [powK_codeE, codeE_eq_oneK] at h
  rw [← hM5.map_powE hx, h, hM5.map_one]

theorem code_of_pow_eq_one {x : E} (hx : validE x = true) {n : Nat} (h : ιF x ^ n = 1) :
    powK (codeE x) n = oneK := by
  rw [powK_codeE, codeE_eq_oneK]
  apply hM5.inj _ _ (hM5.valid_powE hx n) hM5.valid_one
  rw [hM5.map_powE hx, h, hM5.map_one]

theorem pwF_spec {B M p : Nat} (h : pwF B M p = true) {j : Nat} (hj : j < M) :
    Nat.beq (powK (powK (f20 B j) p) p) oneK = true → Nat.beq (powK (f20 B j) p) oneK = true := by
  have := (allN_iff _ _).1 h j hj
  rw [letB_eq, orB_eq, Bool.or_eq_true, Bool.not_eq_true'] at this
  intro h1
  rcases this with h2 | h2
  · rw [h1] at h2
    exact absurd h2 (by decide)
  · exact h2

theorem pow_part {z c : E} (hz : validE z = true) (hc : validE c = true) {k p : Nat} (hk : k < 5)
    (hpw : pwF (CB.getD k 0) (CM.getD k 0) p = true)
    (hw : powE z p = conjE c (decE (RP.getD k 0))) (hz2 : ιF z ^ (p * p) = 1) : ιF z ^ p = 1 := by
  obtain ⟨hrk, -, -, hcen, -⟩ := cls_glue k hk
  set R := decE (RP.getD k 0)
  have hci := hM5.valid_inv _ hc
  set z' := conjE (invE c) z with hz'
  have hz'v : validE z' = true := hM5.valid_conjE hci hz
  have hRc : ιF R = (ιF c)⁻¹ * ιF z ^ p * ιF c := by
    have := congrArg ιF hw
    rw [hM5.map_powE hz, hM5.map_conjE hc hrk] at this
    rw [this]
    group
  have hcomm : mulE z' R = mulE R z' := by
    apply hM5.inj _ _ (hM5.valid_mul _ _ hz'v hrk) (hM5.valid_mul _ _ hrk hz'v)
    rw [hM5.map_mul _ _ hz'v hrk, hM5.map_mul _ _ hrk hz'v, hz', hM5.map_conjE hci hz,
      hM5.map_inv _ hc, hRc]
    group
  obtain ⟨j, hj, hje⟩ := mem_decL.1 ((hcen z' hz'v).1 hcomm)
  have hcode : f20 (CB.getD k 0) j = codeE z' := by
    rw [← hje, codeE_decE (validK_lt (cb_valid k hk j hj))]
  have hpow : ∀ n, ιF z' ^ n = (ιF c)⁻¹ * ιF z ^ n * ιF c := fun n => by
    rw [hz', hM5.map_conjE hci hz, hM5.map_inv _ hc, conj_pow, inv_inv]
  have h9 : ιF z' ^ (p * p) = 1 := by
    rw [hpow, hz2]
    group
  have hval := hM5.valid_powE hz'v p
  have h1 : Nat.beq (powK (powK (f20 (CB.getD k 0) j) p) p) oneK = true := by
    rw [hcode, powK_codeE, code_of_pow_eq_one hval (by rw [hM5.map_powE hz'v, ← pow_mul, h9])]
    exact Nat.beq_refl _
  have h2 := pwF_spec hpw hj h1
  rw [hcode, beq_iff_eq'] at h2
  have h3 := pow_eq_one_of_code hz'v h2
  rw [hpow] at h3
  calc ιF z ^ p = ιF c * ((ιF c)⁻¹ * ιF z ^ p * ιF c) * (ιF c)⁻¹ := by group
    _ = 1 := by
      rw [h3]
      group

theorem pow_28800 {e : E} (he : validE e = true) : ιF e ^ 28800 = 1 := by
  have := pow_card_eq_one' (G := vSub hM5) (x := ⟨ιF e, e, he, rfl⟩)
  rw [hK5] at this
  simpa using congrArg Subtype.val this

theorem pow2_part {e : E} (he : validE e = true) : (ιF e ^ 225) ^ 8 = 1 := by
  obtain ⟨-, -, -, hVS0, -, hnd, hlen, h1S, -, -, hmul, hinv, -⟩ := baseCheck_spec base_check
  obtain ⟨P, hP⟩ := hM5.exists_sub hVS0 h1S hmul hinv
  have hmemP : ∀ t, t ∈ P ↔ ∃ x ∈ S0, ιF x = t := fun t => by
    rw [← SetLike.mem_coe, hP]
    exact mem_S
  have hPK : P ≤ vSub hM5 := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := (hmemP t).1 ht
    exact ⟨x, hVS0 x hx, rfl⟩
  have hPc : Nat.card P = 2 ^ 7 := by
    rw [FiveStdBase.natCard_eq_of_coe P hP, FiveStdBase.natCard_S hM5 hVS0 hnd, hlen]
    norm_num
  have hPe : ∀ t ∈ P, t ^ 8 = 1 := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := (hmemP t).1 ht
    apply pow_eq_one_of_code (hVS0 x hx)
    exact (beq_iff_eq' _ _).1 (List.all_eq_true.1 ex_s0 (codeE x) ((mem_S0 x).1 hx))
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgj : ιF (powE e 225) ^ (2 ^ 7) = 1 := by
    rw [hM5.map_powE he, ← pow_mul]
    exact pow_28800 he
  have := pow_of_sub hM5 hK5 hPK hPc (by norm_num) hPe (hM5.valid_powE he 225) hgj
  rwa [hM5.map_powE he] at this

theorem pow3_part {e : E} (he : validE e = true) : (ιF e ^ 3200) ^ 3 = 1 := by
  have hz := hM5.valid_powE he 3200
  have hz9 : ιF (powE e 3200) ^ (3 * 3) = 1 := by
    rw [hM5.map_powE he, ← pow_mul]
    exact pow_28800 he
  rw [← hM5.map_powE he]
  by_cases hw1 : powE (powE e 3200) 3 = oneE
  · rw [← hM5.map_powE hz, hw1, hM5.map_one]
  · have hw3 : powE (powE (powE e 3200) 3) 3 = oneE := by
      apply hM5.inj _ _ (hM5.valid_powE (hM5.valid_powE hz 3) 3) hM5.valid_one
      rw [hM5.map_powE (hM5.valid_powE hz 3), hM5.map_powE hz, ← pow_mul, hz9, hM5.map_one]
    obtain ⟨k, hk3, hk5, c, hc, hwc⟩ := conj_rep3 (hM5.valid_powE hz 3) hw3 hw1
    have hpw : pwF (CB.getD k 0) (CM.getD k 0) 3 = true := by
      rcases (by omega : k = 3 ∨ k = 4) with rfl | rfl
      · exact ex_cb3
      · exact ex_cb4
    exact pow_part hz hc hk5 hpw hwc hz9

theorem pow5_part {e : E} (he : validE e = true) : (ιF e ^ 1152) ^ 5 = 1 := by
  have hz := hM5.valid_powE he 1152
  have hz25 : ιF (powE e 1152) ^ (5 * 5) = 1 := by
    rw [hM5.map_powE he, ← pow_mul]
    exact pow_28800 he
  rw [← hM5.map_powE he]
  have hw := hM5.valid_powE hz 5
  by_cases hw1 : powE (powE e 1152) 5 = oneE
  · rw [← hM5.map_powE hz, hw1, hM5.map_one]
  · have hw5 : powE (powE (powE e 1152) 5) 5 = oneE := by
      apply hM5.inj _ _ (hM5.valid_powE hw 5) hM5.valid_one
      rw [hM5.map_powE hw, hM5.map_powE hz, ← pow_mul, hz25, hM5.map_one]
    have hord : ordE (powE (powE e 1152) 5) = 5 := by
      rcases (pow5_iff hM5 hw).2 hw5 with h | h
      · exfalso
        apply hw1
        have ho := hM5.orderOf_of_ordE hw h (by norm_num)
        rw [orderOf_eq_one_iff] at ho
        exact hM5.inj _ _ hw hM5.valid_one (by rw [ho, hM5.map_one])
      · exact h
    obtain ⟨k, hk, c, hc, hwc⟩ := conj_rep hw hord
    have hpw : pwF (CB.getD k 0) (CM.getD k 0) 5 = true := by
      interval_cases k
      · exact ex_cb0
      · exact ex_cb1
      · exact ex_cb2
    exact pow_part hz hc (by omega) hpw hwc hz25

theorem pow240 {e : E} (he : validE e = true) : ιF e ^ 240 = 1 :=
  pow240_of_parts _ (pow_28800 he) (by rw [show 16 = 8 * 2 by rfl, pow_mul, pow2_part he, one_pow])
    (pow3_part he) (pow5_part he)

theorem noInv1 : (Cs.all fun e => !(ordE e % 2 != 0 && ordE e % 5 != 0) || ordE e == 1 || ordE e == 3) =
    true := by
  rw [List.all_eq_true]
  intro e heC
  have he := (mem_Cs_iff e).1 heC
  have hd := orderOf_dvd_of_pow_eq_one (pow240 he)
  have hpos : 1 ≤ orderOf (ιF e) := Nat.pos_of_dvd_of_pos hd (by norm_num)
  have hle := Nat.le_of_dvd (by norm_num) hd
  rw [hM5.ordE_of_orderOf he rfl hpos (by omega)]
  have key : ∀ n < 241, n ∣ 240 → (!(n % 2 != 0 && n % 5 != 0) || n == 1 || n == 3) = true := by
    decide +kernel
  exact key _ (by omega) hd

theorem noInv_tori (H0 : List E) (k : Nat) (hk : k = 0 ∨ k = 2) (hH : H0.map codeE = HT k) :
    noInvCheck H0 = true := by
  unfold noInvCheck
  rw [Bool.and_eq_true]
  exact ⟨noInv1, noInv2_tori H0 k hk hH⟩

end CertificateChecks.FiveStd

end
