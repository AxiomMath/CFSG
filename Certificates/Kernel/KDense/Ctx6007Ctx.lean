module

public import Certificates.Data.CFSGNative.MonsterAxis.Basic
import CFSG.Certificates.Kernel.KDense.KeysSound
import CFSG.Certificates.Kernel.KDense.Data.Checks
import CFSG.Certificates.Kernel.KDense.Data.KeySort

public section

namespace CertificateChecks.KernelKDense

open CFSG.Monster.AxisCount.Native

theorem foldl_insert_getElem?_of_ne (f : Nat → Nat) (k : Nat) :
    ∀ (l : List Nat) (m : Std.HashMap Nat Nat), (∀ q ∈ l, f q ≠ k) →
      (l.foldl (fun m p => m.insert (f p) p) m)[k]? = m[k]?
  | [], _, _ => rfl
  | a :: l, m, h => by
    rw [List.foldl_cons, foldl_insert_getElem?_of_ne f k l _ fun q hq => h q (List.mem_cons_of_mem _ hq),
      Std.HashMap.getElem?_insert]
    simp [h a List.mem_cons_self]

theorem foldl_insert_getElem? (f : Nat → Nat) :
    ∀ (l : List Nat) (m : Std.HashMap Nat Nat), l.Nodup → (∀ p ∈ l, ∀ q ∈ l, f p = f q → p = q) →
      ∀ p ∈ l, (l.foldl (fun m p => m.insert (f p) p) m)[f p]? = some p
  | [], _, _, _, p, hp => absurd hp List.not_mem_nil
  | a :: l, m, hnd, hinj, p, hp => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [foldl_insert_getElem?_of_ne f _ l _ ?_, Std.HashMap.getElem?_insert_self]
      intro q hq hfq
      obtain rfl := hinj q (List.mem_cons_of_mem _ hq) p List.mem_cons_self hfq
      exact (List.nodup_cons.1 hnd).1 hq
    · exact foldl_insert_getElem? f l _ (List.nodup_cons.1 hnd).2
        (fun p hp q hq => hinj p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)) p hp

theorem mkCtx_keys : (mkCtx ()).keys = (Array.range 98280).map (keyAt (thetaTab ())) := rfl

theorem mkCtx_pos : (mkCtx ()).pos = mkPos (mkCtx ()).keys := by
  simp only [mkCtx, mkCtxOf]

theorem mkCtx_keys_size : (mkCtx ()).keys.size = 98280 := by
  rw [mkCtx_keys, Array.size_map, Array.size_range]

theorem ctx_keys_getElem! {p : Nat} (hp : p < 98280) :
    (mkCtx ()).keys[p]! = keyAt (thetaTab ()) p := by
  rw [mkCtx_keys, getElem!_pos _ p (by rw [Array.size_map, Array.size_range]; exact hp),
    Array.getElem_map, Array.getElem_range]

theorem keyAt_facts :
    (∀ p < 98280, (keyAt (thetaTab ()) p).1 < 4096 ∧ (keyAt (thetaTab ()) p).2 < 4096) ∧
    ∀ p < 98280, ∀ q < 98280, keyAt (thetaTab ()) p = keyAt (thetaTab ()) q → p = q :=
  CFSG.KC.KDense.keys_sound CFSG.KD.KDF.F CFSG.KD.KDF.KT CFSG.KD.KDF.TH CFSG.KD.KDF.OCT
    CFSG.KD.KDF.DU1 CFSG.KD.KDK.NK CFSG.KD.KDF.th_ok CFSG.KD.KDF.oct_ok CFSG.KD.KDF.du1_ok
    CFSG.KD.KDF.keys_ok CFSG.KD.KDF.keyPlanes_ok CFSG.KD.KDK.keys_distinct

theorem mkCtx_key_spec (p : Nat) (hp : p < 98280) :
    (mkCtx ()).keys[p]!.1 < 4096 ∧ (mkCtx ()).keys[p]!.2 < 4096 ∧
      (mkCtx ()).find (mkCtx ()).keys[p]!.1 (mkCtx ()).keys[p]!.2 = p := by
  have hb : ∀ q < 98280, (mkCtx ()).keys[q]!.1 < 4096 ∧ (mkCtx ()).keys[q]!.2 < 4096 := by
    intro q hq
    rw [ctx_keys_getElem! hq]
    exact keyAt_facts.1 q hq
  refine ⟨(hb p hp).1, (hb p hp).2, ?_⟩
  have hinj : ∀ q ∈ List.range 98280, ∀ q' ∈ List.range 98280,
      keyCode (mkCtx ()).keys[q]!.1 (mkCtx ()).keys[q]!.2 =
        keyCode (mkCtx ()).keys[q']!.1 (mkCtx ()).keys[q']!.2 → q = q' := by
    intro q hq q' hq' h
    rw [List.mem_range] at hq hq'
    obtain ⟨h1, h2⟩ := hb q hq
    obtain ⟨h1', h2'⟩ := hb q' hq'
    unfold keyCode at h
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h1', Nat.mod_eq_of_lt h2'] at h
    have he : (mkCtx ()).keys[q]! = (mkCtx ()).keys[q']! := Prod.ext (by omega) (by omega)
    rw [ctx_keys_getElem! hq, ctx_keys_getElem! hq'] at he
    exact keyAt_facts.2 q hq q' hq' he
  have h := foldl_insert_getElem? (fun q => keyCode (mkCtx ()).keys[q]!.1 (mkCtx ()).keys[q]!.2)
    (List.range 98280) ∅ List.nodup_range hinj p (List.mem_range.2 hp)
  unfold Ctx.find
  rw [mkCtx_pos, mkPos, Std.HashMap.getD_eq_getD_getElem?, h, Option.getD_some]

end CertificateChecks.KernelKDense

end
