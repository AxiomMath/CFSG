module

public import CFSG.Certificates.Kernel.Spor.Fi24OrbSound
public import Certificates.Kernel.Sporadic.Fi24Orb.Data
import CFSG.Certificates.Kernel.Common.ForallChunks
import Certificates.Kernel.Sporadic.Fi24Orb.V0
import Certificates.Kernel.Sporadic.Fi24Orb.V1
import Certificates.Kernel.Sporadic.Fi24Orb.V2
import Certificates.Kernel.Sporadic.Fi24Orb.V3
import Certificates.Kernel.Sporadic.Fi24Orb.V4
import Certificates.Kernel.Sporadic.Fi24Orb.V5
import Certificates.Kernel.Sporadic.Fi24Orb.V6
import Certificates.Kernel.Sporadic.Fi24Orb.V7
import Certificates.Kernel.Sporadic.Fi24Orb.V8
import Certificates.Kernel.Sporadic.Fi24Orb.V9
import Certificates.Kernel.Sporadic.Fi24Orb.V10
import Certificates.Kernel.Sporadic.Fi24Orb.V11
import Certificates.Kernel.Sporadic.Fi24Orb.B0
import Certificates.Kernel.Sporadic.Fi24Orb.B1
import Certificates.Kernel.Sporadic.Fi24Orb.B2
import Certificates.Kernel.Sporadic.Fi24Orb.B3
import Certificates.Kernel.Sporadic.Fi24Orb.B4
import Certificates.Kernel.Sporadic.Fi24Orb.B5
import Certificates.Kernel.Sporadic.Fi24Orb.F0
import Certificates.Kernel.Sporadic.Fi24Orb.F1
import Certificates.Kernel.Sporadic.Fi24Orb.FS
import Certificates.Kernel.Sporadic.Fi24Orb.S
public import CFSG.Certificates.Kernel.LceSP.Cosets
public import CFSG.Certificates.Kernel.Spor.Mat3Sound

public section

namespace CFSG.KD.Fi24Orb

open CFSG.KC.Fi24Orb CFSG.KC.Fi24OrbS CFSG.KC.Fi24FixK

#kc_forall_chunks forAll (fun c => forOK FD CFSG.KD.Fi24Fix.S CFSG.KD.Fi24Fix.TG (nat_lit 306936)
  (nat_lit 64) (nat_lit 1) (Nat.mul (nat_lit 1024) c) = true) 300 CFSG.KD.Fi24Orb.for_ 1024
#kc_forall_chunks inSAll (fun c => inSOK FD CFSG.KD.Fi24Fix.S (nat_lit 31671)
  (Nat.mul (nat_lit 4096) c) = true) 8 CFSG.KD.Fi24Orb.fs_ 4096
#kc_forall_chunks vtAll (fun c => vtOK VT CFSG.KD.Fi24Fix.TG VW (nat_lit 306936)
  (Nat.mul (nat_lit 512) c) = true) 600 CFSG.KD.Fi24Orb.vt_ 512
#kc_forall_chunks bindAll (fun c => bindOK OL NM NI VT CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Fix.AW
  (nat_lit 306936) (Nat.mul (nat_lit 512) c) = true) 600 CFSG.KD.Fi24Orb.bind_ 512
#kc_forall_chunks slpAll (fun c => slpOK MUL3 VLD3 RS IJ (nat_lit 120) (Nat.mul (nat_lit 16) c) = true)
  8 CFSG.KD.Fi24Orb.slp_ 16

theorem split_idx {r b n : ℕ} (hb : 0 < b) (hr : r < n) :
    Nat.mul b (r / b) + r % b = r ∧ r % b < b := by
  refine ⟨?_, Nat.mod_lt _ hb⟩
  change b * (r / b) + r % b = r
  exact Nat.div_add_mod r b

theorem forest_all : ∀ r, 1 ≤ r → r < 306936 →
    ForP FD CFSG.KD.Fi24Fix.S CFSG.KD.Fi24Fix.TG 306936 64 1 r := by
  intro r h1 hr
  obtain ⟨e, hm⟩ := split_idx (b := 1024) (by decide) hr
  have hc : r / 1024 < 300 := by omega
  have := forOK_spec (forAll (r / 1024) hc) (r % 1024) hm (by rw [e]; exact h1)
    (by rw [e]; exact hr)
  rwa [e] at this

theorem inS_all : ∀ j < 31671, fComp (FD (CFSG.KD.Fi24Fix.S j)) = 2 := by
  intro j hj
  obtain ⟨e, hm⟩ := split_idx (b := 4096) (by decide) hj
  have hc : j / 4096 < 8 := by omega
  have := inSOK_spec (inSAll (j / 4096) hc) (j % 4096) hm (by rw [e]; exact hj)
  rwa [e] at this

theorem vt_all : ∀ r < 306936, walk CFSG.KD.Fi24Fix.TG VW r = VT r := by
  intro r hr
  obtain ⟨e, hm⟩ := split_idx (b := 512) (by decide) hr
  have hc : r / 512 < 600 := by omega
  have := vtOK_spec (vtAll (r / 512) hc) (r % 512) hm (by rw [e]; exact hr)
  rwa [e] at this

theorem bind_all : ∀ k < 306936,
    BindP OL NM NI VT CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Fix.AW 306936 k := by
  intro k hk
  obtain ⟨e, hm⟩ := split_idx (b := 512) (by decide) hk
  have hc : k / 512 < 600 := by omega
  have := bindOK_spec (bindAll (k / 512) hc) (k % 512) hm (by rw [e]; exact hk)
  rwa [e] at this

theorem slp_all : ∀ k < 120, VLD3 (RS k) = true ∧
    (2 ≤ k → ∃ i < k, ∃ j < k, MUL3 (RS i) (RS j) = RS k) := by
  intro k hk
  obtain ⟨e, hm⟩ := split_idx (b := 16) (by decide) hk
  have hc : k / 16 < 8 := by omega
  have := slpOK_spec (slpAll (k / 16) hc) (k % 16) hm (by rw [e]; exact hk)
  rwa [e] at this

end CFSG.KD.Fi24Orb

end
