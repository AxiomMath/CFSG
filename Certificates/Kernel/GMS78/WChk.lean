module

public import Certificates.Kernel.GMS78.WData
public import CFSG.Certificates.Kernel.GMS78RuWSound
public import Certificates.Data.GMS78RuPi7RuData
public import CFSG.Certificates.Kernel.Orders.Ru.Data.Const
public import CFSG.Certificates.Kernel.Orders.Ru.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.W

open CFSG.KC.Ord CFSG.KC.GMSW CFSG.ComponentClassification.GMS78.RuPi7

theorem roots : rootsOK RG (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 4704) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H) (nat_lit 1) (nat_lit 10) = true := by quickRfl

theorem invs : invsOK RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 4704) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H) (nat_lit 9) CFSG.KD.OrdRu.ONE = true := by
  quickRfl

theorem bindA : Nat.beq (RG (nat_lit 1)) (CFSG.KD.OrdRu.RW (nat_lit 1)) = true := by quickRfl

theorem bindB : Nat.beq (RG (nat_lit 2)) (CFSG.KD.OrdRu.RW (nat_lit 2)) = true := by quickRfl

theorem RI_bd : relsBounded RI (nat_lit 9) = true := by quickRfl

theorem RI_len : Nat.beq (lenRels RI) (nat_lit 7) = true := by quickRfl

theorem RI_bind : relsEqK RI (mkImgK pi7RuImgWords.toList (nat_lit 0)) = true := by quickRfl

theorem RI_c0 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 2) = true := by
  quickRfl

theorem RI_c1 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 2) (nat_lit 1) = true := by
  quickRfl

theorem RI_c2 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 3) (nat_lit 1) = true := by
  quickRfl

theorem RI_c3 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 4) (nat_lit 1) = true := by
  quickRfl

theorem RI_c4 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 5) (nat_lit 1) = true := by
  quickRfl

theorem RI_c5 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 6) (nat_lit 1) = true := by
  quickRfl

theorem RI_all : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 7) = true :=
  relsAll_join (c := nat_lit 7) (relsAll_join (c := nat_lit 6) (relsAll_join (c := nat_lit 5) (relsAll_join (c := nat_lit 4) (relsAll_join (c := nat_lit 3) (RI_c0) RI_c1 rfl rfl) RI_c2 rfl rfl) RI_c3 rfl rfl) RI_c4 rfl rfl) RI_c5 rfl rfl

theorem RC_bd : relsBounded RC (nat_lit 9) = true := by quickRfl

theorem RC_len : Nat.beq (lenRels RC) (nat_lit 37) = true := by quickRfl

theorem RC_bind : relsEqK RC (mkCodesK relsC) = true := by quickRfl

theorem RC_c0 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RC (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 33) = true := by
  quickRfl

theorem RC_c1 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RC (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 33) (nat_lit 4) = true := by
  quickRfl

theorem RC_all : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RC (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 37) = true :=
  relsAll_join (c := nat_lit 37) (RC_c0) RC_c1 rfl rfl

theorem RA_bd : relsBounded RA (nat_lit 9) = true := by quickRfl

theorem RA_len : Nat.beq (lenRels RA) (nat_lit 31) = true := by quickRfl

theorem RA_bind : relsEqK RA (mkCodesK relsA) = true := by quickRfl

theorem RA_c0 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RA (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 31) = true := by
  quickRfl

theorem RA_all : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RA (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 31) = true :=
  RA_c0

theorem RE_bd : relsBounded RE (nat_lit 9) = true := by quickRfl

theorem RE_len : Nat.beq (lenRels RE) (nat_lit 28) = true := by quickRfl

theorem RE_bind : relsEqK RE (mkCodesK relsE) = true := by quickRfl

theorem RE_c0 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RE (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 28) = true := by
  quickRfl

theorem RE_all : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RE (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 28) = true :=
  RE_c0

theorem RS_bd : relsBounded RS (nat_lit 9) = true := by quickRfl

theorem RS_len : Nat.beq (lenRels RS) (nat_lit 2) = true := by quickRfl

theorem RS_bind : relsEqK RS (mkSurjK pi7RuSurjWords.toList (nat_lit 0)) = true := by quickRfl

theorem RS_c0 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RS (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 2) = true := by
  quickRfl

theorem RS_all : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RS (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 2) = true :=
  RS_c0

end CertificateChecks.KernelGMS78.W

end
