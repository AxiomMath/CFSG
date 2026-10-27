module

public import Certificates.Data.Kernel.RootOrbit.Check
public import Certificates.Kernel.RootOrbit.Data
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit

public section

open CFSG.KC.RootOrbit CFSG.KD.RootOrbit CFSG.HardMathSupport.Timmesfeld.RootAut

namespace CertificateChecks.KernelRootOrbit

theorem rowsA2 : rowsOf (CartanMatrix.A 2) = rowsZ rA2 := by decide +kernel
theorem rowsA3 : rowsOf (CartanMatrix.A 3) = rowsZ rA3 := by decide +kernel
theorem rowsA4 : rowsOf (CartanMatrix.A 4) = rowsZ rA4 := by decide +kernel
theorem rowsA5 : rowsOf (CartanMatrix.A 5) = rowsZ rA5 := by decide +kernel
theorem rowsA6 : rowsOf (CartanMatrix.A 6) = rowsZ rA6 := by decide +kernel
theorem rowsA7 : rowsOf (CartanMatrix.A 7) = rowsZ rA7 := by decide +kernel
theorem rowsA8 : rowsOf (CartanMatrix.A 8) = rowsZ rA8 := by decide +kernel
theorem rowsD4 : rowsOf (CartanMatrix.D 4) = rowsZ rD4 := by decide +kernel
theorem rowsD5 : rowsOf (CartanMatrix.D 5) = rowsZ rD5 := by decide +kernel
theorem rowsD6 : rowsOf (CartanMatrix.D 6) = rowsZ rD6 := by decide +kernel
theorem rowsD7 : rowsOf (CartanMatrix.D 7) = rowsZ rD7 := by decide +kernel
theorem rowsD8 : rowsOf (CartanMatrix.D 8) = rowsZ rD8 := by decide +kernel
theorem rowsE6 : rowsOf (CartanMatrix.E 6) = rowsZ rE6 := by decide +kernel

theorem certA2 : rootCertB (rowsZ rA2) 2 pA2 wA2 6 = true := by decide +kernel
theorem certA3 : rootCertB (rowsZ rA3) 3 pA3 wA3 12 = true := by decide +kernel
theorem certA4 : rootCertB (rowsZ rA4) 4 pA4 wA4 20 = true := by decide +kernel
theorem certA5 : rootCertB (rowsZ rA5) 5 pA5 wA5 30 = true := by decide +kernel
theorem certA6 : rootCertB (rowsZ rA6) 6 pA6 wA6 42 = true := by decide +kernel
theorem certA7 : rootCertB (rowsZ rA7) 7 pA7 wA7 56 = true := by decide +kernel
theorem certA8 : rootCertB (rowsZ rA8) 8 pA8 wA8 72 = true := by decide +kernel
theorem certD4 : rootCertB (rowsZ rD4) 4 pD4 wD4 24 = true := by decide +kernel
theorem certD5 : rootCertB (rowsZ rD5) 5 pD5 wD5 40 = true := by decide +kernel
theorem certD6 : rootCertB (rowsZ rD6) 6 pD6 wD6 60 = true := by decide +kernel
theorem certD7 : rootCertB (rowsZ rD7) 7 pD7 wD7 84 = true := by decide +kernel
theorem certD8 : rootCertB (rowsZ rD8) 8 pD8 wD8 112 = true := by decide +kernel
theorem certE6 : rootCertB (rowsZ rE6) 6 pE6 wE6 72 = true := by decide +kernel

theorem sepA1 : sepB (CartanMatrix.A 1) 2 = true := by decide +kernel
theorem sepB2 : sepB (CartanMatrix.B 2) 4 = true := by decide +kernel
theorem sepB3 : sepB (CartanMatrix.B 3) 6 = true := by decide +kernel
theorem sepB4 : sepB (CartanMatrix.B 4) 8 = true := by decide +kernel
theorem sepB5 : sepB (CartanMatrix.B 5) 10 = true := by decide +kernel
theorem sepB6 : sepB (CartanMatrix.B 6) 12 = true := by decide +kernel
theorem sepB7 : sepB (CartanMatrix.B 7) 14 = true := by decide +kernel
theorem sepB8 : sepB (CartanMatrix.B 8) 16 = true := by decide +kernel
theorem sepC3 : sepB (CartanMatrix.C 3) 6 = true := by decide +kernel
theorem sepC4 : sepB (CartanMatrix.C 4) 8 = true := by decide +kernel
theorem sepC5 : sepB (CartanMatrix.C 5) 10 = true := by decide +kernel
theorem sepC6 : sepB (CartanMatrix.C 6) 12 = true := by decide +kernel
theorem sepC7 : sepB (CartanMatrix.C 7) 14 = true := by decide +kernel
theorem sepC8 : sepB (CartanMatrix.C 8) 16 = true := by decide +kernel
theorem sepE7 : sepB (CartanMatrix.E 7) 14 = true := by decide +kernel
theorem sepE8 : sepB (CartanMatrix.E 8) 16 = true := by decide +kernel
theorem sepF4 : sepB CartanMatrix.F₄ 8 = true := by decide +kernel
theorem sepG2 : sepB CartanMatrix.G₂.transpose 4 = true := by decide +kernel

end CertificateChecks.KernelRootOrbit
