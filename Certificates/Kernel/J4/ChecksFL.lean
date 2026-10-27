module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S

theorem fl1_0 : Nat.beq (runF kd (nat_lit 1) FL1_0 (nat_lit 0)) FLB1_0 = true := by quickRfl

theorem fl1_1 : Nat.beq (runF kd (nat_lit 1) FL1_1 FLB1_0) FLB1_1 = true := by quickRfl

theorem fl1_2 : Nat.beq (runF kd (nat_lit 1) FL1_2 FLB1_1) FLB1_2 = true := by quickRfl

theorem fl1_3 : Nat.beq (runF kd (nat_lit 1) FL1_3 FLB1_2) FLB1_3 = true := by quickRfl

theorem fl1_4 : Nat.beq (runF kd (nat_lit 1) FL1_4 FLB1_3) FLB1_4 = true := by quickRfl

theorem fl1_5 : Nat.beq (runF kd (nat_lit 1) FL1_5 FLB1_4) FLB1_5 = true := by quickRfl

theorem fl1_6 : Nat.beq (runF kd (nat_lit 1) FL1_6 FLB1_5) (fullOf kd) = true := by quickRfl

theorem fl2_0 : Nat.beq (runF kd (Nat.succ (nat_lit 1)) FL2_0 (nat_lit 0)) FLB2_0 = true := by quickRfl

theorem fl2_1 : Nat.beq (runF kd (Nat.succ (nat_lit 1)) FL2_1 FLB2_0) FLB2_1 = true := by quickRfl

theorem fl2_2 : Nat.beq (runF kd (Nat.succ (nat_lit 1)) FL2_2 FLB2_1) FLB2_2 = true := by quickRfl

theorem fl2_3 : Nat.beq (runF kd (Nat.succ (nat_lit 1)) FL2_3 FLB2_2) FLB2_3 = true := by quickRfl

theorem fl2_4 : Nat.beq (runF kd (Nat.succ (nat_lit 1)) FL2_4 FLB2_3) FLB2_4 = true := by quickRfl

theorem fl2_5 : Nat.beq (runF kd (Nat.succ (nat_lit 1)) FL2_5 FLB2_4) FLB2_5 = true := by quickRfl

theorem fl2_6 : Nat.beq (runF kd (Nat.succ (nat_lit 1)) FL2_6 FLB2_5) (fullOf kd) = true := by quickRfl

theorem fl3_0 : Nat.beq (runF kd (Nat.succ (Nat.succ (nat_lit 1))) FL3_0 (nat_lit 0)) FLB3_0 = true := by quickRfl

theorem fl3_1 : Nat.beq (runF kd (Nat.succ (Nat.succ (nat_lit 1))) FL3_1 FLB3_0) FLB3_1 = true := by quickRfl

theorem fl3_2 : Nat.beq (runF kd (Nat.succ (Nat.succ (nat_lit 1))) FL3_2 FLB3_1) FLB3_2 = true := by quickRfl

theorem fl3_3 : Nat.beq (runF kd (Nat.succ (Nat.succ (nat_lit 1))) FL3_3 FLB3_2) FLB3_3 = true := by quickRfl

theorem fl3_4 : Nat.beq (runF kd (Nat.succ (Nat.succ (nat_lit 1))) FL3_4 FLB3_3) FLB3_4 = true := by quickRfl

theorem fl3_5 : Nat.beq (runF kd (Nat.succ (Nat.succ (nat_lit 1))) FL3_5 FLB3_4) FLB3_5 = true := by quickRfl

theorem fl3_6 : Nat.beq (runF kd (Nat.succ (Nat.succ (nat_lit 1))) FL3_6 FLB3_5) (fullOf kd) = true := by quickRfl

theorem fl4_0 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))) FL4_0 (nat_lit 0)) FLB4_0 = true := by quickRfl

theorem fl4_1 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))) FL4_1 FLB4_0) FLB4_1 = true := by quickRfl

theorem fl4_2 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))) FL4_2 FLB4_1) FLB4_2 = true := by quickRfl

theorem fl4_3 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))) FL4_3 FLB4_2) FLB4_3 = true := by quickRfl

theorem fl4_4 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))) FL4_4 FLB4_3) FLB4_4 = true := by quickRfl

theorem fl4_5 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))) FL4_5 FLB4_4) FLB4_5 = true := by quickRfl

theorem fl4_6 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))) FL4_6 FLB4_5) (fullOf kd) = true := by quickRfl

theorem fl5_0 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1))))) FL5_0 (nat_lit 0)) FLB5_0 = true := by quickRfl

theorem fl5_1 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1))))) FL5_1 FLB5_0) FLB5_1 = true := by quickRfl

theorem fl5_2 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1))))) FL5_2 FLB5_1) FLB5_2 = true := by quickRfl

theorem fl5_3 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1))))) FL5_3 FLB5_2) FLB5_3 = true := by quickRfl

theorem fl5_4 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1))))) FL5_4 FLB5_3) FLB5_4 = true := by quickRfl

theorem fl5_5 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1))))) FL5_5 FLB5_4) FLB5_5 = true := by quickRfl

theorem fl5_6 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1))))) FL5_6 FLB5_5) (fullOf kd) = true := by quickRfl

theorem fl6_0 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))))) FL6_0 (nat_lit 0)) FLB6_0 = true := by quickRfl

theorem fl6_1 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))))) FL6_1 FLB6_0) FLB6_1 = true := by quickRfl

theorem fl6_2 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))))) FL6_2 FLB6_1) FLB6_2 = true := by quickRfl

theorem fl6_3 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))))) FL6_3 FLB6_2) FLB6_3 = true := by quickRfl

theorem fl6_4 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))))) FL6_4 FLB6_3) FLB6_4 = true := by quickRfl

theorem fl6_5 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))))) FL6_5 FLB6_4) FLB6_5 = true := by quickRfl

theorem fl6_6 : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))))) FL6_6 FLB6_5) (fullOf kd) = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
