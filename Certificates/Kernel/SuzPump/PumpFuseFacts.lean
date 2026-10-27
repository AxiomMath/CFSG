module

public import Certificates.Kernel.SuzPump.PumpFacts
public import Certificates.Kernel.SuzPump.PumpFuseR
public import Certificates.Kernel.SuzPump.PumpFuseE
public import Certificates.Kernel.Sporadic.OddCore.S8147R
import CFSG.Certificates.Kernel.Spor.TextSound
import CFSG.Certificates.Kernel.SporSch.DerivsSound
import CFSG.Certificates.Kernel.SporSch.PairJ3FaithSound
import CFSG.Certificates.Kernel.Child3Reps
import CFSG.Sporadic.Schreier.Co3Restrict
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.HNOddCore.FourPairA

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzPump

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor
open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2 (allLt_iff)

theorem tab_size : (fuseTab ()).size = 300 := by simp [fuseTab]

theorem hexLine_append (b c : ByteArray) {L : Nat} (h : (L + 1) * (3 * 14 + 1) ≤ b.size + 1) :
    hexLine (b ++ c) 3 14 L = hexLine b 3 14 L := by
  unfold hexLine
  apply Array.ext (by simp)
  intro i h1 h2
  simp only [Array.getElem_ofFn]
  have hi : i < 14 := by simpa using h1
  have hle : L * (3 * 14 + 1) + 3 * i + 3 ≤ b.size := by nlinarith
  exact CFSG.KS.SporSch.PF2.hexAt_append_left b c _ 3 hle

theorem tab_get {j : Nat} (hj : j < 300) : (fuseTab ())[j]! = unpack 14 11 (FR j) := by
  have hb := CFSG.KS.Text.hexBind_sound fbind j hj
  have hl := CFSG.KS.SporSch.hexBind_layout fbind (w' := 3) (n' := 14) rfl
  have es : String.ofList (FT.chars ++ ['\n']) = fuseText ++ "\n" := by
    rw [String.ofList_append, ← FT.eq]
  rw [es, CFSG.KS.SporSch.PF2.toUTF8_append, Nat.zero_add] at hb
  rw [es, CFSG.KS.SporSch.PF2.toUTF8_append] at hl
  have hsz : (fuseText.toUTF8 ++ "\n".toUTF8).size = 300 * (3 * 14 + 1) := by
    unfold layoutOK at hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    exact hl.1
  have hnl : "\n" = "".push '\n' := by decide
  have h1 : "\n".toUTF8.size = 1 := by
    rw [hnl, String.toUTF8_eq_toByteArray, String.size_toByteArray, String.utf8ByteSize_push, String.utf8ByteSize_empty,
      Nat.zero_add]
    exact Char.utf8Size_eq_one_iff.2 (by decide)
  rw [ByteArray.size_append, h1] at hsz
  have e : (fuseTab ())[j]! = fuseRow j := by
    rw [fuseTab, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  rw [e, fuseRow, ← hb]
  generalize fuseText.toUTF8 = b at hsz ⊢
  exact (hexLine_append b _ (by omega)).symm

theorem rebK_congr_gen {n w : Nat} {LR TR TRI B B' : Nat → Nat} (m : Nat)
    (h : ∀ l < m, B l = B' l) :
    rebK n w LR TR TRI B m = rebK n w LR TR TRI B' m := by
  induction m with
  | zero => simp only [rebK, List.range_zero, List.foldl_nil]
  | succ m ih =>
    have e : ∀ C : Nat → Nat, rebK n w LR TR TRI C (m + 1) =
        rebStep n w LR TR TRI C (rebK n w LR TR TRI C m) m := fun C => by
      simp only [rebK, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, e, ih fun l hl => h l (by omega)]
    unfold rebStep
    rw [h m (by omega)]

theorem rebK_congr {B B' : Nat → Nat} : ∀ m, (∀ l < m, B l = B' l) →
    rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI B m = rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI B' m :=
  fun m h => rebK_congr_gen m h

theorem ext_get {R s l : Nat} (hl : l < 6) (hs : s + 6 ≤ 14) :
    ((unpack 14 11 R).extract s (s + 6))[l]! = pg 11 (mask 11) R (s + l) := by
  rw [getElem!_pos _ l (by simp [unpack]; omega), Array.getElem_extract,
    ← getElem!_pos (unpack 14 11 R) (s + l) (by simp [unpack]; omega),
    CFSG.KC.Child3.unpack_get' (by omega)]

theorem row_ok {j : Nat} (hj : j < 300) : rowK j = true := by
  have hb : j / 10 < 30 := by omega
  have h := FRK.all (j / 10) hb
  unfold rowsB at h
  have := (Orb.allN_iff.1 h) (j % 10) (by omega)
  rwa [Nat.div_add_mod] at this

theorem okP_of_sift {X : Nat} (h : siftOK X = true) : okP (levels ()) (unpack 1782 11 X) = true ∧
    permB 1782 11 X = true := by
  unfold siftOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨okP_unpack ⟨h1, h2, h4⟩ h3, h3⟩

theorem row_facts {j : Nat} (hj : j < 300) :
    rebuild (levels ()) ((fuseTab ())[j]!.extract 1 7) = unpack 1782 11 (FTS j) ∧
    rebuild (levels ()) ((fuseTab ())[j]!.extract 7 13) = unpack 1782 11 (FNS j) ∧
    siftOK (FTS j) = true ∧ siftOK (FNS j) = true ∧
    permOK 1782 11 (mask 11) (1782 * 11) (FNS j) (pinvS 1782 11 (mask 11) (FNS j)) = true ∧
    Nat.beq (cm 1782 11 (FNS j) (cm 1782 11 (FTS j) (pinvS 1782 11 (mask 11) (FNS j))))
      (if Nat.beq (pg 11 (mask 11) (FR j) 13) 0 then XA else YY) = true := by
  have h := row_ok hj
  unfold rowK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨ht, hn⟩, et⟩, en⟩, st⟩, sn⟩, pn⟩, hc⟩ := h
  have bt : ∀ l < 6, ((fuseTab ())[j]!.extract 1 7)[l]! = pg 11 (mask 11) (FR j) (l + 1) := by
    intro l hl
    rw [tab_get hj, ext_get (s := 1) hl (by norm_num), Nat.add_comm]
  have bn : ∀ l < 6, ((fuseTab ())[j]!.extract 7 13)[l]! = pg 11 (mask 11) (FR j) (l + 7) := by
    intro l hl
    rw [tab_get hj, ext_get (s := 7) hl (by norm_num), Nat.add_comm]
  have rt : reb ((fuseTab ())[j]!.extract 1 7) =
      rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => pg 11 (mask 11) (FR j) (l + 1)) 6 :=
    rebK_congr 6 bt
  have rn : reb ((fuseTab ())[j]!.extract 7 13) =
      rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => pg 11 (mask 11) (FR j) (l + 7)) 6 :=
    rebK_congr 6 bn
  refine ⟨?_, ?_, st, sn, pn, hc⟩
  · rw [rebuild_eq (by rw [rt]; exact ht), rt, Nat.eq_of_beq_eq_true et]
  · rw [rebuild_eq (by rw [rn]; exact hn), rn, Nat.eq_of_beq_eq_true en]

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b :=
  Bool.eq_iff_iff.2 (by rw [beq_iff_eq, Nat.beq_eq])

theorem ts_get {j : Nat} (hj : j < 300) :
    ((fuseTab ()).map fun r => rebuild (levels ()) (r.extract 1 7))[j]! = unpack 1782 11 (FTS j) := by
  rw [getElem!_pos _ j (by simp [tab_size]; omega), Array.getElem_map,
    ← getElem!_pos (fuseTab ()) j (by rw [tab_size]; omega)]
  exact (row_facts hj).1

theorem ns_get {j : Nat} (hj : j < 300) :
    ((fuseTab ()).map fun r => rebuild (levels ()) (r.extract 7 13))[j]! = unpack 1782 11 (FNS j) := by
  rw [getElem!_pos _ j (by simp [tab_size]; omega), Array.getElem_map,
    ← getElem!_pos (fuseTab ()) j (by rw [tab_size]; omega)]
  exact (row_facts hj).2.1

theorem tab_entry {j e : Nat} (hj : j < 300) (he : e < 14) :
    ((fuseTab ())[j]!)[e]! = pg 11 (mask 11) (FR j) e := by
  rw [tab_get hj, CFSG.KC.Child3.unpack_get' he]

theorem pX1 : permB 1782 11 (SFvT.F 1) = true := permB_of_pp (S8147.fv_PP (by norm_num))

theorem pg_ppow3 {n w p t : Nat} (hn : n < 2 ^ 32) (hn' : n < 16777216) (hw : n + 1 < 2 ^ w)
    (ht : t < n) : pg w (mask w) (ppow n w (mask w) (pidn n w) p 3) t =
      pg w (mask w) p (pg w (mask w) p (pg w (mask w) p t)) := by
  have e3 : ppow n w (mask w) (pidn n w) p 3 =
      pcomp n w (mask w) p (ppow n w (mask w) (pidn n w) p 2) := CFSG.KS.PF.strictN_eqP _ _
  have e2 : ppow n w (mask w) (pidn n w) p 2 =
      pcomp n w (mask w) p (ppow n w (mask w) (pidn n w) p 1) := CFSG.KS.PF.strictN_eqP _ _
  have e1 : ppow n w (mask w) (pidn n w) p 1 = pcomp n w (mask w) p (pidn n w) :=
    CFSG.KS.PF.strictN_eqP _ _
  rw [e3, CFSG.KS.PF.pg_pcomp hn ht, e2, CFSG.KS.PF.pg_pcomp hn ht, e1,
    CFSG.KS.PF.pg_pcomp hn ht, CFSG.KS.PF.pg_pidn hn' hw ht]

theorem beq_pw3 {n w p t : Nat} (hn : n < 2 ^ 32) (hn' : n < 16777216) (hw : n + 1 < 2 ^ w)
    (ht : t < n) (h : Nat.beq (pg w (mask w) p (pg w (mask w) p (pg w (mask w) p t))) t = false) :
    Nat.beq (pw n w p 3) (pidn n w) = false := by
  cases hb : Nat.beq (pw n w p 3) (pidn n w)
  · rfl
  · exfalso
    have h2 : pg w (mask w) (pw n w p 3) t = t := by
      rw [Nat.eq_of_beq_eq_true hb]
      exact CFSG.KS.PF.pg_pidn hn' hw ht
    unfold pw at h2
    rw [pg_ppow3 hn hn' hw ht] at h2
    rw [h2, Nat.beq_refl] at h
    exact Bool.noConfusion h

theorem elK_of_elQ {i P : Nat} (h : elQ i P = true) : elK i P = true := by
  have key : ∀ t < 1782, mv3 P t = true → elK i P = true := by
    intro t ht hm
    unfold mv3 at hm
    have hb := beq_pw3 (n := 1782) (w := 11) (p := P) (by norm_num) (by norm_num) (by norm_num) ht
      (by simpa using hm)
    unfold elK
    rw [hb]
    rfl
  unfold elQ at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · exact key 0 (by norm_num) h
  · exact key 1 (by norm_num) h
  · exact key 2 (by norm_num) h
  · exact key 3 (by norm_num) h
  · exact h

theorem el_ok {i : Nat} {c : ArrCert} {N : Nat} {T : Nat → Nat} (hs : c.pts.size = N)
    (hT : ∀ k < N, c.pts[k]! = unpack 1782 11 (T k)) (hP : ∀ k < N, CFSG.KC.BfsPin.PP 1782 11 (T k))
    (hE : ∀ k < N, elK i (T k) = true) :
    allLt c.pts.size (fun k =>
      !(eqA 1782 (powArr 1782 c.pts[k]! 3) (idA 1782)) || eqA 1782 c.pts[k]! (idA 1782) ||
        (anyLt (fuseTab ()).size (fun j => ((fuseTab ())[j]!)[0]! == i &&
            eqA 1782 c.pts[k]! ((fuseTab ()).map fun r => rebuild (levels ()) (r.extract 1 7))[j]!) &&
          (i != 0 || !(commA 1782 c.pts[k]! (suzFiveLineArr 1))))) = true := by
  rw [allLt_iff, hs]
  intro k hk
  have hp := permB_of_pp (hP k hk)
  have h := hE k hk
  rw [hT k hk, powEq_id hw hp, eqA_id hw hp, S8147.line_eq (by norm_num), commA_unp hp pX1]
  have hany : anyLt (fuseTab ()).size (fun j => ((fuseTab ())[j]!)[0]! == i &&
      eqA 1782 (unpack 1782 11 (T k))
        ((fuseTab ()).map fun r => rebuild (levels ()) (r.extract 1 7))[j]!) =
      CFSG.KC.LQT.P.anyN 300 (fun j => Nat.beq (pg 11 (mask 11) (FR j) 0) i &&
        Nat.beq (T k) (FTS j)) := by
    apply Bool.eq_iff_iff.2
    rw [CFSG.Sporadic.Schreier.Co3.anyLt_iff, anyNP_eq, List.any_eq_true, tab_size]
    constructor
    · rintro ⟨j, hj, e⟩
      refine ⟨j, List.mem_range.2 hj, ?_⟩
      have hf := (okP_of_sift (row_facts hj).2.2.1).2
      rwa [tab_entry hj (by norm_num), ts_get hj, eqA_unpack' hw hp hf, beq_nat] at e
    · rintro ⟨j, hj, e⟩
      rw [List.mem_range] at hj
      refine ⟨j, hj, ?_⟩
      have hf := (okP_of_sift (row_facts hj).2.2.1).2
      rwa [tab_entry hj (by norm_num), ts_get hj, eqA_unpack' hw hp hf, beq_nat]
  rw [hany]
  have hi : (i != 0) = !Nat.beq i 0 := by rw [bne, beq_nat]
  rw [hi]
  exact h

theorem blk_get {f : Nat → Bool} {F : Nat → Bool} (hF : ∀ b < 6, F b = true)
    (hd : ∀ b, F b = allN 600 (fun r => f (600 * b + r))) {k : Nat} (hk : k < 3600) :
    f k = true := by
  have hb : k / 600 < 6 := by omega
  have h := hF (k / 600) hb
  rw [hd] at h
  have := (Orb.allN_iff.1 h) (k % 600) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

theorem fuse_ok : fuseCheck () = true := by
  have rY : rebuild (levels ()) yTuple = unpack 1782 11 YY := rebuild_eq yrb.1
  have pY := (ysift YY (by simp)).2.2.1
  obtain ⟨f3, f1, fs⟩ := fxa
  have hrows : ∀ j < 300, (okP (levels ())
        ((fuseTab ()).map fun r => rebuild (levels ()) (r.extract 1 7))[j]! &&
      okP (levels ()) ((fuseTab ()).map fun r => rebuild (levels ()) (r.extract 7 13))[j]! &&
      eqA 1782 (conjA 1782 ((fuseTab ()).map fun r => rebuild (levels ()) (r.extract 7 13))[j]!
          ((fuseTab ()).map fun r => rebuild (levels ()) (r.extract 1 7))[j]!)
        (repOf (rebuild (levels ()) xAβ) (yArr (levels ())) ((fuseTab ())[j]!)[13]!)) = true := by
    intro j hj
    obtain ⟨-, -, st, sn, pn, hc⟩ := row_facts hj
    obtain ⟨ot, pt⟩ := okP_of_sift st
    obtain ⟨on, pnn⟩ := okP_of_sift sn
    rw [ts_get hj, ns_get hj, ot, on, conjA_unp pnn pt pn, tab_entry hj (by norm_num)]
    have pc : permB 1782 11 (cm 1782 11 (FNS j) (cm 1782 11 (FTS j) (pinvS 1782 11 (mask 11) (FNS j))))
        = true := permB_pcomp hw pnn (permB_pcomp hw pt (permB_pinvS hw pnn))
    unfold yArr repOf
    rw [rY, hX, beq_nat]
    by_cases h0 : Nat.beq (pg 11 (mask 11) (FR j) 13) 0 = true
    · rw [h0] at hc ⊢
      rw [if_pos rfl, eqA_unpack' hw pc pX]
      simpa using hc
    · rw [Bool.not_eq_true] at h0
      rw [h0] at hc ⊢
      rw [if_neg (by simp), eqA_unpack' hw pc pY]
      simpa using hc
  have hel : ∀ i < 6, allLt (suzFiveCCert i).pts.size (fun k =>
      !(eqA 1782 (powArr 1782 (suzFiveCCert i).pts[k]! 3) (idA 1782)) ||
        eqA 1782 (suzFiveCCert i).pts[k]! (idA 1782) ||
        (anyLt (fuseTab ()).size (fun j => ((fuseTab ())[j]!)[0]! == i &&
            eqA 1782 (suzFiveCCert i).pts[k]!
              ((fuseTab ()).map fun r => rebuild (levels ()) (r.extract 1 7))[j]!) &&
          (i != 0 || !(commA 1782 (suzFiveCCert i).pts[k]! (suzFiveLineArr 1))))) = true := by
    intro i hi
    interval_cases i
    · obtain ⟨-, hs, hT, hP⟩ := S8147.cE0
      exact el_ok hs hT hP fun k hk => elK_of_elQ
        (blk_get (f := fun k => elQ 0 (SFC0.T k)) FE0.all (fun _ => rfl) hk)
    · obtain ⟨-, hs, hT, hP⟩ := S8147.cE1
      exact el_ok hs hT hP fun k hk => Orb.allN_iff.1 fel1 k hk
    · obtain ⟨-, hs, hT, hP⟩ := S8147.cE2
      exact el_ok hs hT hP fun k hk => Orb.allN_iff.1 fel2 k hk
    · obtain ⟨-, hs, hT, hP⟩ := S8147.cE3
      exact el_ok hs hT hP fun k hk => elK_of_elQ
        (blk_get (f := fun k => elQ 3 (SFC3.T k)) FE3.all (fun _ => rfl) hk)
    · obtain ⟨-, hs, hT, hP⟩ := S8147.cE4
      exact el_ok hs hT hP fun k hk => elK_of_elQ
        (blk_get (f := fun k => elQ 4 (SFC4.T k)) FE4.all (fun _ => rfl) hk)
    · obtain ⟨-, hs, hT, hP⟩ := S8147.cE5
      exact el_ok hs hT hP fun k hk => Orb.allN_iff.1 fel5 k hk
  unfold fuseCheck fuseCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hX]
    exact (okP_of_sift fs).1
  · rw [hX, powEq_id hw pX]
    exact f3
  · rw [hX, eqA_id hw pX]
    exact f1
  · rw [tab_size, allLt_iff]
    exact hrows
  · rw [allLt_iff]
    exact hel

end CertificateChecks.KernelSuzPump

end
