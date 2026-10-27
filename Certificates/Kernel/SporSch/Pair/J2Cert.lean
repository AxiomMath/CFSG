
module

public import Certificates.Kernel.SporSch.Pair.J2Faith
public import Certificates.Kernel.SporSch.Pair.GenSyl
public import CFSG.Certificates.Kernel.SporSch.PairSylEnc
public import CFSG.Sporadic.Schreier.PairJ2CertInputs
meta import CFSG.Sporadic.Schreier.PairJ2CertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.PJ2Sy CFSG.Sporadic.Schreier.j2SylowsText

#kss_sylp CertificateChecks.KernelSporSch.PJ2Sy CFSG.Sporadic.Schreier.j2Sylows 9

namespace CertificateChecks.KernelSporSch.PJ2Cert

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.SporSch.PSylEnc
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairText
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch

theorem vlt : allN 315 (fun i => allN 14 (fun j => Nat.blt (pg 4 (mask 4) (PJ2VT i) j) 5)) = true := by
  quickRfl

theorem tok : tokK PJ2Sy.chars (encSyl 315 9 PJ2Sy.R) = true := by quickRfl

theorem syl : sylsK 315 9 PJ2Sy.R = true := by quickRfl

theorem primes : ((PJ2Sy.R.map (toSyl 315 9)).toArray.toList.map fun e => e.prime) == [2, 3, 5, 7] := by
  decide +kernel

theorem gcount : ((PJ2Sy.R.map (toSyl 315 9)).toArray.toList.map fun e => e.gens.size) ==
    [7, 3, 2, 1] := by
  decide +kernel

theorem rcount : ((PJ2Sy.R.map (toSyl 315 9)).toArray.toList.map fun e => e.records.size) ==
    [35, 13, 6, 1] := by
  decide +kernel

theorem syl_eq : j2Sylows = (PJ2Sy.R.map (toSyl 315 9)).toArray := by
  rw [j2Sylows, PJ2Sy.eq, tokK_sound tok, parse_encSyl]

theorem perm_j2 {P : Nat} (h : permK 315 9 P = true) : j2PermOK (unpack 315 9 P) = true := by
  have hI := invEqK_sound (n := 315) (w := 9) (p := P) (r := pinvS 315 9 (mask 9) P) h
  unfold j2PermOK
  rw [hI.1, hI.2]
  simp [unpack]

theorem perms_j2 {Ps : List Nat} (h : permsK 315 9 Ps = true) :
    (Ps.map (unpack 315 9)).toArray.all j2PermOK = true := by
  rw [List.all_toArray, List.all_eq_true]
  intro x hx
  obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
  exact perm_j2 (permsK_mem h P hP)

theorem rec_ok (r : RecP) (h : recK 315 9 r = true) : j2RecordOK (toRec 315 9 r) = true := by
  obtain ⟨rp, cj, ⟨g, b, s, wd⟩⟩ := r
  change bAnd(permK 315 9 rp, bAnd(lettersK cj, bAnd(Nat.ble (lenK g) (lenK s), bAnd(ltL 315 b,
    bAnd(nodupK b, bAnd(permsK 315 9 s, bAnd(prefK g s,
      Nat.beq (Nat.add (lenK wd) (lenK g)) (lenK s)))))))) = true at h
  obtain ⟨h1, h⟩ := bAnd_tt h
  obtain ⟨h2, h⟩ := bAnd_tt h
  obtain ⟨k1, h⟩ := bAnd_tt h
  obtain ⟨k2, h⟩ := bAnd_tt h
  obtain ⟨k3, h⟩ := bAnd_tt h
  obtain ⟨k4, h⟩ := bAnd_tt h
  obtain ⟨k5, k6⟩ := bAnd_tt h
  rw [lenK_eq, lenK_eq] at k1
  rw [lenK_eq, lenK_eq, lenK_eq] at k6
  have hle : g.length ≤ s.length := Nat.le_of_ble_eq_true k1
  have hw : wd.length + g.length = s.length := Nat.eq_of_beq_eq_true k6
  obtain ⟨_, hpre⟩ := prefK_sound k5
  have c2 : cj.toArray.all (fun w => w.all fun l => l == 1 || l == -1 || l == 2 || l == -2) = true := by
    rw [List.all_toArray, List.all_eq_true]
    intro x hx
    rw [List.all_eq_true]
    exact lettersK_sound h2 x hx
  have c4 : b.all (· < 315) = true := by
    rw [List.all_eq_true]
    intro x hx
    exact decide_eq_true (ltL_sound k2 x hx)
  have c7 : (List.range (g.map (unpack 315 9)).toArray.size).all (fun k =>
      (g.map (unpack 315 9)).toArray[k]! == (s.map (unpack 315 9)).toArray[k]!) = true := by
    rw [List.all_eq_true]
    intro k hk
    have hk' : k < g.length := by simpa using hk
    rw [getElem!_pos _ k (by simpa using hk'), getElem!_pos _ k (by simp; omega)]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [hpre k hk' (by omega)]
    exact beq_self_eq_true _
  have c8 : (wd.toArray.size + (g.map (unpack 315 9)).toArray.size ==
      (s.map (unpack 315 9)).toArray.size) = true := by
    simp only [List.size_toArray, List.length_map]
    rw [hw]
    exact beq_self_eq_true _
  unfold j2RecordOK
  simp only [toRec, toChain]
  have c3' : (g.map (unpack 315 9)).toArray.size ≤ (s.map (unpack 315 9)).toArray.size := by
    simp only [List.size_toArray, List.length_map]
    exact hle
  simp only [perm_j2 h1, c2, c3', nodupK_sound k3, c4, perms_j2 k4, c7, c8, decide_true,
    Bool.and_self]

theorem recs_ok (rs : List RecP)
    (h : List.rec (motive := fun _ => Bool) true (fun r _ ih2 => bAnd(recK 315 9 r, ih2)) rs = true) :
    (rs.map (toRec 315 9)).toArray.all j2RecordOK = true := by
  rw [List.all_toArray, List.all_eq_true]
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  clear hx
  induction rs with
  | nil => simp at hr
  | cons r' rs ih =>
    obtain ⟨q1, q2⟩ := bAnd_tt h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact rec_ok _ q1
    · exact ih q2 hr

theorem all_ok (R : List SylP) (h : sylsK 315 9 R = true) : (R.map (toSyl 315 9)).toArray.all
    (fun e => e.gens.all j2PermOK && e.records.all j2RecordOK) = true := by
  rw [List.all_toArray, List.all_eq_true]
  intro e he
  obtain ⟨S, hS, rfl⟩ := List.mem_map.1 he
  clear he
  induction R with
  | nil => simp at hS
  | cons S' Ss ih =>
    obtain ⟨h1, h2⟩ := bAnd_tt h
    rcases List.mem_cons.1 hS with rfl | hS
    · obtain ⟨p, g, rs⟩ := S
      change bAnd(permsK 315 9 g, List.rec (motive := fun _ => Bool) true
        (fun r _ ih2 => bAnd(recK 315 9 r, ih2)) rs) = true at h1
      obtain ⟨g1, g2⟩ := bAnd_tt h1
      simp only [toSyl]
      rw [perms_j2 g1, recs_ok rs g2]
      rfl
    · exact ih h2 hS

theorem perm_S (j : Nat) (hj : j < 7) : j2PermOK (j2StrongArrs ())[j]! = true := by
  have hI := invEqK_sound (allN_spec PJ2.perm j hj)
  rw [PJ2.arr_eq j hj]
  unfold j2PermOK
  rw [hI.1, hI.2]
  simp [unpack]

theorem facts : j2CertOK = true := by
  have hS : (j2StrongArrs ()).size = 7 := by simp [j2StrongArrs]
  have c1 : (j2Vectors.size == 315) = true := by
    rw [j2Vectors, PairGen.hexVectors_size]
    rfl
  have c2 : allLt 315 (fun i => CFSG.Sporadic.J1.Native.wfV 5 14 j2Vectors[i]!) = true :=
    PairGen.wfV_of PJ2Faith.vget vlt
  have c3 : ((j2StrongArrs ()).size == 7) = true := by
    rw [hS]
    rfl
  have c4 : allLt 7 (fun j => j2PermOK (j2StrongArrs ())[j]!) = true := by
    rw [allLt_iff]
    exact perm_S
  have c5 : allLt 7 (fun j => isInvA 315 (j2StrongArrs ())[j]! (rawInvs 315 (j2StrongArrs ()))[j]!) =
      true := by
    have h := PairGen.gens_ok hS PJ2.arr_eq PJ2.perm
    rw [allLt_iff] at h ⊢
    intro j hj
    exact ((Bool.and_eq_true _ _).mp (h j hj)).2
  have c6 : ((j2Words ()).size == 7) = true := rfl
  unfold j2CertOK
  rw [syl_eq, c1, c2, c3, c4, c5, c6, primes, gcount, rcount, all_ok _ syl]
  rfl

end CertificateChecks.KernelSporSch.PJ2Cert

end
