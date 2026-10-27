module

public import Certificates.Kernel.He589203.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LocalQT.BaseT
meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.DcK
public import Certificates.Kernel.He7149.Final
public import Certificates.Kernel.E68Spor4215.Final
public import CFSG.Certificates.Kernel.DcKSound
public import CFSG.Certificates.Kernel.DcKParse
public import CFSG.Certificates.Kernel.DcKInv
public import CFSG.Certificates.Kernel.LocalQTBaseSRep
public import CFSG.Certificates.Kernel.SporLatOmegaSound
public import Certificates.Data.DcHeOverV
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He589203

open CFSG.KC.DcK CFSG.KC.E64F CFSG.KC.SLOm CFSG.Quasithin.H13.LocDbl.DcNative
open CFSG.Quasithin.H13.LocDbl.HeCert CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BT CFSG.KC.LQT.PW

theorem rep_of_good {n : Nat} {c : Nat} {t : Array Nat} (h : Good n t (im c)) : Rep n 14 c t :=
  ⟨h.1, fun p hp => ⟨by
      rw [CFSG.QuasithinUnique.K1.SporadicPerm.img, (h.2 p hp).1]; exact (h.2 p hp).2,
    by rw [CFSG.QuasithinUnique.K1.SporadicPerm.img, (h.2 p hp).1]; rfl⟩⟩

theorem nodes_eq {n w : Nat} {prog : List (Nat × Nat)} {TF : Nat → Nat} {K : Nat}
    (hnd : ∀ c < K, nodesT n w prog TF (c * 8) 8 = true) (hK : prog.length + 2 ≤ K * 8) :
    ∀ q < prog.length, TF (2 + q) =
      mulW n w (TF (prog.getD q (0, 0)).1) (TF (prog.getD q (0, 0)).2) := by
  intro q hq
  have hc : (2 + q) / 8 < K := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  have := CFSG.KC.LQT.RW.Pf.allR_true (hnd _ hc) ((2 + q) % 8) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod'] at this
  dsimp only at this
  have h2 : CFSG.KC.Ord.andB (Nat.ble 2 (2 + q)) (Nat.blt (2 + q)
      (Nat.add (CFSG.KC.LQT.L.lenA prog) 2)) = true := by
    rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, lenA_eq, Nat.add_eq]
    constructor <;> omega
  have := CFSG.KC.LQT.BS.Pf.impB_true this h2
  rw [CFSG.KC.LQT.P.beq_iff, CFSG.KC.LQT.BS.Pf.nthP_eq,
    show Nat.sub (2 + q) 2 = q by rw [Nat.sub_eq]; omega] at this
  exact this

theorem slp_rep {ta tb : Array Nat} {prog : List (Nat × Nat)} {TF : Nat → Nat} {K : Nat}
    (ha : Rep 8330 14 (TF 0) ta) (hb : Rep 8330 14 (TF 1) tb) (hv : slpValidAux prog 2 = true)
    (hnd : ∀ c < K, nodesT 8330 14 prog TF (c * 8) 8 = true) (hK : prog.length + 2 ≤ K * 8) :
    ∀ j < prog.length + 2, Rep 8330 14 (TF j) (slpTabsA ta tb prog)[j]! := by
  intro j hj
  have hs : (slpTabsA ta tb prog).size = prog.length + 2 := by
    rw [slpTabsA, CFSG.KC.LQT.BS.Pf.foldl_slpStepA_size]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  rw [slpTabsA]
  refine CFSG.KC.LQT.BS.Pf.slpTF_rep prog #[ta, tb] (fun i hi => ?_) hv
    (fun q hq => nodes_eq hnd hK q hq) j (by rw [← slpTabsA, hs]; exact hj)
  rcases i with _ | _ | i
  · exact ha
  · exact hb
  · simp at hi

theorem elems_all {n : Nat} {B : List Nat} {G : Nat → Nat → Nat} {m : Nat} {E : EnumK}
    {lo len : Nat} (h : elemsK n B G m E lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → elemK n B G m E k = true := by
  intro k h1 h2
  unfold elemsK at h
  rw [List.all_eq_true] at h
  exact h k (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem getD_range_map (f : Nat → Nat) {N k : Nat} (hk : k < N) :
    ((List.range N).map f).toArray.getD k 0 = f k := by
  simp [Array.getD_eq_getD_getElem?, hk]

theorem some_getD {α : Type} {o : Option α} (h : o.isSome = true) (d : α) :
    o = some (o.getD d) := by
  cases o with
  | none => simp at h
  | some x => rfl

end CFSG.KD.He589203

end
