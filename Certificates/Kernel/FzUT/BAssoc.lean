module

public import Certificates.Data.Kernel.FzUT.BAssoc
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.FzBMod

theorem ch441796_rho : rhoB = true := by quickRfl

theorem ch441796_rhoMul : rhoMulB = true := by quickRfl

theorem ch441796_homQ (c : Bool) : tabHomB (tqT c) = true := by cases c <;> quickRfl

theorem ch441796_homS (c : Bool) : tabHomB (tsT c) = true := by cases c <;> quickRfl

theorem ch441796_homY (c : Bool) : tabHomB (tyT c) = true := by cases c <;> quickRfl

theorem ch441796_actComp (c : Bool) : actCompB c = true := by cases c <;> quickRfl

theorem ch441796_amAssoc : amAssocB = true := by quickRfl

theorem ch441796_id (c : Bool) : idB c = true := by cases c <;> quickRfl

end CFSG.KC.FzBMod
