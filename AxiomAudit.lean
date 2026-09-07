import FltVandiver

/-!
Axiom audit: the flt-vandiver proof engine
Run with:  lake env lean AxiomAudit.lean
Expected axiom base: [propext, Classical.choice, Quot.sound]
-/

#print axioms FltVandiver.Descent95.fermatLastTheoremFor_of_certs_95
#print axioms FltVandiver.Descent95.fermatLastTheoremFor_of_certs_95'
#print axioms FltVandiver.fermatLastTheorem_of_vandiver_caseI
#print axioms FltVandiver.fermatLastTheorem_of_vandiver_sgAux
#print axioms FltVandiver.fermatLastTheorem_of_vandiver_window
#print axioms FltVandiver.Descent95.caseII_95_top
#print axioms FltVandiver.Descent95.caseII_95_int
#print axioms FltVandiver.caseI_of_auxiliaryPrime
#print axioms FltVandiver.caseI_of_sgCert
#print axioms FltVandiver.QiCert.Fast2.vandiverCert_of_fast2
#print axioms FltVandiver.JointAux.fermatLastTheoremFor_of_joint_cert
#print axioms FltVandiver.JointAux.fermatLastTheorem_of_joint_supply
#print axioms FltVandiver.BadCert.fermatLastTheoremFor_of_bad_cert
#print axioms FltVandiver.BadCert.fermatLastTheorem_of_bad_supply
#print axioms FltVandiver.BadCert.noBad_of_two_mul_le
#print axioms FltVandiver.BadCert.fermatLastTheoremFor_of_size_cert
