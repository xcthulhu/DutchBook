theory Extended_Classical_Propositional_Logic
  imports "../../Intuitionistic/Intuitionistic_Logic"
begin

class Extended_Classical_Propositional_Logic = Classical_Propositional_Logic + Intuitionistic_Logic

theorem (in Extended_Classical_Propositional_Logic) Formula_Maximally_Consistent_Set_biconditional:
  assumes "\<phi>-MCS \<Omega>"
  shows "(\<psi> \<leftrightarrow> \<chi>) \<in> \<Omega> = (\<psi> \<in> \<Omega> \<longleftrightarrow> \<chi> \<in> \<Omega>)"
proof -
  {
    assume "\<psi> \<in> \<Omega> \<longleftrightarrow> \<chi> \<in> \<Omega>"
    hence "(\<psi> \<leftrightarrow> \<chi>) \<in> \<Omega>"
      by (meson assms
                Biconditional_Introduction [where \<phi>="\<psi>" and \<psi>="\<chi>"]
                Formula_Maximally_Consistent_Set_reflection [where \<Gamma>="\<Omega>"]
                Formula_Maximally_Consistent_Set_implication
                set_deduction_weaken)
  }
  thus ?thesis
    using assms
          Formula_Maximally_Consistent_Set_biconditional_elimination
    by metis
qed

end
