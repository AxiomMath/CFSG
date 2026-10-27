module

public import Certificates.Kernel.ThCent.LDefs
public import Certificates.Kernel.ThPump.Data
public import Certificates.Data.Kernel.ThPump.Defs

public section

namespace CFSG.KD.ThPump

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent CFSG.KC.ThPump CFSG.KD.ThCent.L

@[expose] noncomputable def invL (r e : Nat) : Nat := powB ThS.c ThS.rm ThS.ONE (V5 r) e (nat_lit 5)

theorem comm_19 : Nat.beq (mulB ThS.c ThS.rm (V5 19) C5) (mulB ThS.c ThS.rm C5 (V5 19)) = true := by
  decide +kernel
theorem comm_99 : Nat.beq (mulB ThS.c ThS.rm (V5 99) C5) (mulB ThS.c ThS.rm C5 (V5 99)) = true := by
  decide +kernel
theorem comm_114 :
    Nat.beq (mulB ThS.c ThS.rm (V5 114) C5) (mulB ThS.c ThS.rm C5 (V5 114)) = true := by
  decide +kernel
theorem comm_115 :
    Nat.beq (mulB ThS.c ThS.rm (V5 115) C5) (mulB ThS.c ThS.rm C5 (V5 115)) = true := by
  decide +kernel

theorem cube_19 : Nat.beq (powB ThS.c ThS.rm ThS.ONE (V5 19) 3 (nat_lit 5)) ThS.ONE = true := by
  decide +kernel
theorem ne_19 : neB ThS.c ThS.rm ThS.ONE (V5 19) ThS.ONE = true := by decide +kernel

theorem inv_19 : Nat.beq (mulB ThS.c ThS.rm (V5 19) (invL 19 2)) ThS.ONE = true := by decide +kernel
theorem inv_99 : Nat.beq (mulB ThS.c ThS.rm (V5 99) (invL 99 19)) ThS.ONE = true := by
  decide +kernel
theorem inv_114 : Nat.beq (mulB ThS.c ThS.rm (V5 114) (invL 114 2)) ThS.ONE = true := by
  decide +kernel
theorem inv_115 : Nat.beq (mulB ThS.c ThS.rm (V5 115) (invL 115 19)) ThS.ONE = true := by
  decide +kernel

theorem lets_ok : letsOK P.U = true := by decide +kernel
theorem len_ok : P.U.length = 100 := by decide +kernel
theorem dist_ok : distinctL P.D = true := by decide +kernel

theorem rows_ok :
    strictF (V5 19) (fun a => strictF (V5 99) fun b => strictF (V5 114) fun c =>
      strictF (V5 115) fun d => strictF (invL 19 2) fun ia => strictF (invL 99 19) fun ib =>
        strictF (invL 114 2) fun ic => strictF (invL 115 19) fun id =>
          rowsOK ThS.rm (selL a b c d) (selL ia ib ic id) a P.U P.D) = true := by
  decide +kernel

end CFSG.KD.ThPump

end
