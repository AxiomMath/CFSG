module

public import Certificates.Kernel.SmithD6Uw.Checks
public import Certificates.Kernel.SmithD6Wt.Facts
public import CFSG.Certificates.Kernel.SmithD6UwSound

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Uw

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KD.SmithD6
  CertificateChecks.SmithD6Wt

theorem nthR_eq : ∀ (cs : List (List (Nat × Nat))) (c : Nat), nthR cs c = cs.getD c []
  | [], _ => by
    change [] = _
    simp
  | _ :: _, 0 => rfl
  | _ :: cs, c + 1 => by
    change nthR cs c = _
    rw [nthR_eq cs c]
    simp

theorem uwRec_all : ∀ p (hp : p < J.wt64C.flatten.length),
    ∃ r, uwRecOK p J.wt64C.flatten[p] r = true := by
  have h64 : J.wt64C.length = 37 := by rw [← lenC_eq, wt64C_lenC]
  intro p hp
  obtain ⟨l, hl, hs⟩ := List.mem_flatten.1 (List.getElem_mem hp)
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hl
  obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hs
  have hc37 : c < 37 := by rw [h64] at hc; exact hc
  obtain ⟨hf, -, -⟩ := chunkOK_sound hc (wt64Chunks_ok c hc37)
  have hpj : p = 2048 * c + j := by
    have h1 := hf j hj
    rw [hjs, wt64_facts.2.2.1 p hp] at h1
    omega
  have hO := uwOrbChunks_ok c hc37
  rw [uwOrbOK, nthC_eq, nthR_eq, getD_eq hc] at hO
  obtain ⟨hlen, hrec⟩ := uwOrbGo_sound _ _ _ hO
  have hrl : c < JU.uwRC.length := by rw [uwRC_length]; exact hc37
  rw [getD_eq hrl] at hlen hrec
  refine ⟨(JU.uwRC[c])[j]'(by rw [hlen]; exact hj), ?_⟩
  have := hrec j hj (by rw [hlen]; exact hj)
  rw [← hjs, hpj]
  exact this

theorem uwCls_eq (p : Nat) (hp : p < J.wt64C.flatten.length) :
    pkGet JU.uwK 2 p = uwClsK J.wt64C.flatten[p] := by
  obtain ⟨r, hr⟩ := uwRec_all p hp
  exact (uwRecOK_sound hr).1

theorem uwFirst (p : Nat) (hp : p < J.wt64C.flatten.length) : uwRep (pkGet JU.uwK 2 p) ≤ p := by
  obtain ⟨r, hr⟩ := uwRec_all p hp
  exact (uwRecOK_sound hr).2.1

def uwStep (a b : Nat) : Prop :=
  ∃ g < 45, pkGet JU.uwK 2 a = pkGet JU.uwK 2 b ∧ ∃ (ha : a < J.wt64C.flatten.length)
    (hb : b < J.wt64C.flatten.length),
    liftT (JU.uwT.getD g []) J.wt64C.flatten[a] = J.wt64C.flatten[b]

theorem uwReach : ∀ v < J.wt64C.flatten.length,
    Relation.ReflTransGen uwStep (uwRep (pkGet JU.uwK 2 v)) v := by
  suffices H : ∀ n, ∀ v < J.wt64C.flatten.length, pkGet JU.uwD 5 v ≤ n →
      Relation.ReflTransGen uwStep (uwRep (pkGet JU.uwK 2 v)) v from
    fun v hv => H _ v hv le_rfl
  intro n
  induction n with
  | zero =>
    intro v hv hd
    obtain ⟨r, hr⟩ := uwRec_all v hv
    have := (uwRecOK_sound hr).2.2.1
    omega
  | succ n ih =>
    intro v hv hd
    obtain ⟨r, hr⟩ := uwRec_all v hv
    obtain ⟨-, -, hpos, hroot, hstep⟩ := uwRecOK_sound hr
    by_cases h1 : pkGet JU.uwD 5 v = 1
    · rw [← hroot h1]
    · obtain ⟨hg, hl, p, hfind, -, hdp, hkp⟩ := hstep h1
      obtain ⟨hp, hpx⟩ := wt64_facts.2.2.2 r.2 p hfind
      have ihp := ih p hp (by omega)
      rw [hkp] at ihp
      refine Relation.ReflTransGen.tail ihp ⟨r.1, hg, hkp, hp, hv, ?_⟩
      rw [hpx, hl]

end CertificateChecks.SmithD6Uw

end
