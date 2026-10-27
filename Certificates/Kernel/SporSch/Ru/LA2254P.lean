
module

public import Certificates.Kernel.SporSch.Ru.LA2254R
public import Certificates.Kernel.SporSch.Ru.LA2254O0
public import Certificates.Kernel.SporSch.Ru.LA2254O1
public import Certificates.Kernel.SporSch.Ru.LA2254O2
public import Certificates.Kernel.SporSch.Ru.LA2254O3
public import Certificates.Kernel.SporSch.Ru.LB2255P
public import Certificates.Kernel.SporSch.Ru.LWit
public import CFSG.Certificates.Kernel.SporSch.Ru2254Sound
import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Ru2250 CFSG.KS.Ru2254 CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLB

theorem pos_lt {i : Nat} (hi : i < 3) :
    (ruZLPos.getD i (0, 0)).1 < rcnt (RuLS.LR 0) ∧ (ruZLPos.getD i (0, 0)).2 < rcnt (RuLS.LR 1) := by
  rw [cL0, cL1]
  interval_cases i <;> decide

theorem y0_lt {i : Nat} (hi : i < 3) : ∀ x < 4060, pg 12 (mask 12) (Y0 i) x < 4060 :=
  tr_lt RuLS.hl (i := 0) (by norm_num) (pos_lt hi).1

theorem y1_lt {i : Nat} (hi : i < 3) : ∀ x < 4060, pg 12 (mask 12) (Y1 i) x < 4060 :=
  tr_lt RuLS.hl (i := 1) (by norm_num) (pos_lt hi).2

theorem zl_eq {i : Nat} (hi : i < 3) :
    ruZLA i = compA 4060 (unpack 4060 12 (Y0 i)) (unpack 4060 12 (Y1 i)) := by
  rw [ruZLA, show ruLevL = rawLevels 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) from rfl,
    prod2A_eq RuL.binds RuLS.head RuLS.hl (le_refl 2) (pos_lt hi).1 (pos_lt hi).2]
  rfl

theorem comms : ∀ i < 3, ∀ j < 3, ruCommTest (ruZLA i) ruLGensA[j]! = true := by
  intro i hi j hj
  have h := allN_spec comm i hi
  rw [PackFld.strictB_eqP, PackFld.strictB_eqP] at h
  have hX : ∀ x < 4060, pg 12 (mask 12) (RuW.LG j) x < 4060 := fun x hx =>
    Nat.blt_eq.mp (allN_spec (range_of_permOK (allN_spec RuLW.pLG j hj)) x hx)
  rw [zl_eq hi, comm_eq' (y0_lt hi) (y1_lt hi)
    (fun x hx => by rw [RuW.lg_eq hj, Orb.unpack_get hx]) hX]
  exact allN_spec h j hj

theorem orbAll : ∀ k < 19, orbOK k = true := by
  intro k hk
  have h5 : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : k / 5 = 0 ∨ k / 5 = 1 ∨ k / 5 = 2 ∨ k / 5 = 3) with h | h | h | h
  · have h' := O0.all (k % 5) h5
    have ek : Nat.add (Nat.mul 5 0) (k % 5) = k := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rwa [orb0, orbP, ek] at h'
  · have h' := O1.all (k % 5) h5
    have ek : Nat.add (Nat.mul 5 1) (k % 5) = k := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rwa [orb1, orbP, ek] at h'
  · have h' := O2.all (k % 5) h5
    have ek : Nat.add (Nat.mul 5 2) (k % 5) = k := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rwa [orb2, orbP, ek] at h'
  · have h4 : k % 5 < 4 := by omega
    have h' := O3.all (k % 5) h4
    have ek : Nat.add (Nat.mul 5 3) (k % 5) = k := by simp only [Nat.add_eq, Nat.mul_eq]; omega
    rwa [orb3, orbP, ek] at h'

theorem orbFix_eq {k : Nat} (hk : k < 19) : ruLOrbFix (ruRepZA k) = inv (Nat.mul 7 k) := by
  have hc := orbAll k hk
  unfold orbOK at hc
  rw [PackFld.strictB_eqP, PackFld.strictB_eqP] at hc
  have hl : ruLevL = rawLevels 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) := rfl
  have h2 := count2_eq RuL.binds RuLS.head RuLS.hl (le_refl 2)
    (p := fun l => (ruRepZA k)[l[0]!]! == l[0]!) (P := pOF k) fun a ha b hb => by
      have h0 := tr_lt RuLS.hl (i := 0) (by norm_num) ha
      have h1 := tr_lt RuLS.hl (i := 1) (by norm_num) hb
      rw [comp_get h1 (by norm_num : 0 < 4060), tk_get hk (tv_lt h0 h1 (by norm_num)), beq_nat]
      unfold pOF
      rw [PackFld.strictB_eqP]
  rw [cL0, cL1] at h2
  rw [← Nat.eq_of_beq_eq_true hc, ruLOrbFix, hl, h2]
  rfl

theorem yt_get {i k : Nat} (hi : i < 3) (hk : k < 19) {x : Nat} (hx : x < 4060) :
    (compA 4060 (ruZLA i) (ruRepZA k))[x]! = ytK i k x := by
  rw [zl_eq hi, compA_get hx, tk_get hk hx, comp_get (y1_lt hi) (tk_lt hk x hx)]
  rfl

theorem yt_lt {i k : Nat} (hi : i < 3) (hk : k < 19) {x : Nat} (hx : x < 4060) :
    ytK i k x < 4060 := tv_lt (y0_lt hi) (y1_lt hi) (tk_lt hk x hx)

theorem fix_eq {i k : Nat} (hi : i < 3) (hk : k < 19) :
    ruFixCnt (compA 4060 (ruZLA i) (ruRepZA k)) =
        inv (Nat.add (Nat.mul 7 k) (Nat.add 1 (Nat.mul 2 i))) ∧
      ruFixCnt (compA 4060 (compA 4060 (ruZLA i) (ruRepZA k)) (compA 4060 (ruZLA i) (ruRepZA k))) =
        inv (Nat.add (Nat.mul 7 k) (Nat.add 2 (Nat.mul 2 i))) := by
  obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec fix k hk) i hi)
  refine ⟨?_, ?_⟩
  · rw [ruFixCnt, fixedList_length_eq fun x hx => yt_get hi hk hx]
    exact Nat.eq_of_beq_eq_true e1
  · rw [ruFixCnt, fixedList_length_eq (f := fun x => ytK i k (ytK i k x)) fun x hx => by
      rw [compA_get hx, yt_get hi hk hx, yt_get hi hk (yt_lt hi hk hx)]]
    exact Nat.eq_of_beq_eq_true e2

theorem inv_eq {k : Nat} (hk : k < 19) : ruLInv (ruRepZA k) = inv (Nat.mul 7 k) ::
    (List.range 3).flatMap fun i => [inv (Nat.add (Nat.mul 7 k) (Nat.add 1 (Nat.mul 2 i))),
      inv (Nat.add (Nat.mul 7 k) (Nat.add 2 (Nat.mul 2 i)))] := by
  rw [ruLInv, orbFix_eq hk]
  refine congrArg (List.cons _) (List.flatMap_congr fun i hi => ?_)
  have hi3 : i < 3 := List.mem_range.1 hi
  rw [(fix_eq hi3 hk).1, (fix_eq hi3 hk).2]

theorem nodupINV : ((List.range 19).map fun k => inv (Nat.mul 7 k) ::
    (List.range 3).flatMap fun i => [inv (Nat.add (Nat.mul 7 k) (Nat.add 1 (Nat.mul 2 i))),
      inv (Nat.add (Nat.mul 7 k) (Nat.add 2 (Nat.mul 2 i)))]).Nodup := by
  decide +kernel

theorem nodup : ((List.range 19).map fun k => ruLInv (ruRepZA k)).Nodup := by
  rw [List.map_congr_left fun k hk => inv_eq (List.mem_range.1 hk)]
  exact nodupINV

theorem facts : (∀ i < 3, ∀ j < 3, ruCommTest (ruZLA i) ruLGensA[j]! = true) ∧
    ((List.range 19).map fun k => ruLInv (ruRepZA k)).Nodup :=
  ⟨comms, nodup⟩

end CertificateChecks.KernelSporSch.RuLA

end
