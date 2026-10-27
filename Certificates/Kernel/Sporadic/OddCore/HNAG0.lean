module

public import Certificates.Kernel.Sporadic.OddCore.HN2092

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HNAG0

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData
open CFSG.ONSchreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.DecLines
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.HN2092

theorem s6_eq : s6Perms = (HNT.S6.E.map List.toArray).toArray := by
  unfold s6Perms
  rw [HNT.S6.eq]
  exact linesOf_of_chk HNT.S6.ok

theorem o6_eq : o6Lists = (HNT.O6.E.map List.toArray).toArray := by
  unfold o6Lists
  rw [HNT.O6.eq]
  exact linesOf_of_chk HNT.O6.ok

theorem s6G : s6Perms.size = 12 ∧
    ∀ s < 12, ∀ x < 8800, (s6Perms[s]!)[x]! = HN2091.genL 8800 HS6R s x := by
  rw [s6_eq]
  exact HN2091.gens_of (by decide +kernel) HN2091.g6_ok

theorem om0L_eq : om0L = Array.ofFn (n := 1100) fun i => r32 HO6_1.PTS i.val := by
  change o6Lists[1]! = _
  rw [o6_eq, HN2091.lines_get]
  exact HN2091.list_r32 (by decide +kernel) HN2091.l61

theorem om0L_size : om0L.size = 1100 := by rw [om0L_eq, Array.size_ofFn]

theorem om0L_get {i : Nat} (hi : i < 1100) : om0L[i]! = r32 HO6_1.PTS i := by
  rw [om0L_eq]
  exact CFSG.KS.PW.ofFn_get' hi

theorem pos_get {j : Nat} (hj : j < 1100) : (posArr 8800 om0L)[r32 HO6_1.PTS j]! = j := by
  have hR : ∀ i < om0L.size, om0L[i]! < 8800 := fun i hi => by
    rw [om0L_size] at hi
    rw [om0L_get hi]
    exact pt_lt hi
  have hd : ∀ i < om0L.size, ∀ j < i, om0L[j]! ≠ om0L[i]! := fun i hi j hji heq => by
    rw [om0L_size] at hi
    rw [om0L_get (by omega), om0L_get hi] at heq
    have e := congrArg (r32 HO6_1.POS) heq
    rw [pt_pos (by omega), pt_pos hi] at e
    omega
  have h := (CFSG.KS.PW.posArr_spec hR hd).2 j (by rw [om0L_size]; exact hj)
  rwa [om0L_get hj] at h

theorem g_get : om0Gens.size = 12 ∧ ∀ s < 12, om0Gens[s]! = unpack 1100 11 (HSG s) := by
  obtain ⟨h6s, h6⟩ := s6G
  refine ⟨by unfold om0Gens; rw [Array.size_map, h6s], fun s hs => ?_⟩
  unfold om0Gens
  rw [getElem!_pos _ s (by rw [Array.size_map, h6s]; exact hs), Array.getElem_map,
    ← getElem!_pos InvData.s6Perms s (by rw [h6s]; exact hs)]
  unfold restrictTab
  refine (CFSG.KS.PW.arr_ext (n := 1100) (F := fun i => pg 11 (mask 11) (HSG s) i)
    (by rw [Array.size_map, om0L_size]) (fun i hi => ?_)).trans rfl
  · rw [getElem!_pos _ i (by rw [Array.size_map, om0L_size]; exact hi), Array.getElem_map,
      ← getElem!_pos om0L i (by rw [om0L_size]; exact hi), om0L_get hi, h6 s hs _ (pt_lt hi)]
    obtain ⟨hb1, hb2⟩ := (CFSG.KS.bAnd_iff _ _).1 (allN_spec (allN_spec gk s hs) i hi)
    rw [Nat.eq_of_beq_eq_true hb2, pos_get (Eq.mp Nat.blt_eq hb1)]

end CertificateChecks.KernelSpor.HNAG0

end
