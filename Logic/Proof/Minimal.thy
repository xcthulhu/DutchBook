section {* Minimal Logic *}
  
theory Minimal
  imports Main
begin

text {* This theory presents \emph{minimal logic}, the implicational fragment of intuitionistic logic. *}

subsection {* Axiomatization *}

text {* Minimal logic is given by the following Hilbert-style axiom system: *}

class Minimal_Logic =
  fixes implication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixr "\<rightarrow>" 70)
  fixes proves :: "'a \<Rightarrow> bool"             ("\<turnstile>\<^sub>M\<^sub>I\<^sub>N _" [60] 55)
  assumes Axiom_1: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  assumes Axiom_2: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  assumes Modus_Ponens: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N \<phi> \<rightarrow> \<psi>  \<Longrightarrow> \<turnstile>\<^sub>M\<^sub>I\<^sub>N \<phi> \<Longrightarrow> \<turnstile>\<^sub>M\<^sub>I\<^sub>N \<psi>" 

text {* One instance is the built-in type {@type "bool"}; instantiating this type establishes
        consistency. *}

interpretation Bool_Minimal_Logic: Minimal_Logic "op \<longrightarrow>" "id"
proof qed (simp)+
  
subsection {* The Deduction Theorem *}
  
text {* Perhaps the most significant result in minimal logic is the \emph{deduction theorem},
        which is a mechanism for handling sets of assumptions.*}

text {* The deduction theorem can be developed naturally in terms of \emph{lists} of assumptions,
        and then shown for the weaker case of sets of assumptions. *}

subsection {* Lists of Assumptions *}  
  
text {* List implication is given recursively as follows: *}  
  
primrec (in Minimal_Logic) list_implication :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<rightarrow>" 80) where
    "[] :\<rightarrow> \<phi> = \<phi>"
  | "(\<psi> # \<Psi>) :\<rightarrow> \<phi> = \<psi> \<rightarrow> \<Psi> :\<rightarrow> \<phi>"

text {* Analogues of the two axioms of minimal logic can be naturally stated using
        list implication. Before giving them, a form of the 
        \emph{hypothetical syllogism} rule is presented for simplifying their proofs. *}

lemma (in Minimal_Logic) hypothetical_syllogism: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N (\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"  
  by (meson Axiom_1 Axiom_2 Modus_Ponens)
    
lemma (in Minimal_Logic) list_implication_Axiom_1: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<phi>"
  by (induct \<Gamma>, (simp, meson Axiom_1 Axiom_2 Modus_Ponens)+)

lemma (in Minimal_Logic) list_implication_Axiom_2: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<Gamma> :\<rightarrow> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<psi>"
  by (induct \<Gamma>, (simp, meson Axiom_1 Axiom_2 Modus_Ponens hypothetical_syllogism)+)

text {* The above two lemmas gives rise to an interpretation of minimal logic, 
        where @{term "\<Gamma>"} plays the role of a \emph{background theory}. *}

context Minimal_Logic begin
interpretation List_Implication_Logic: Minimal_Logic "op \<rightarrow>" "\<lambda> \<phi>. \<turnstile>\<^sub>M\<^sub>I\<^sub>N \<Gamma> :\<rightarrow> \<phi>"
proof qed (meson Axiom_1 Axiom_2 Modus_Ponens list_implication_Axiom_1 list_implication_Axiom_2)+
end
  
text {* Along with the two axioms of minimal logic, there is a \emph{flip} rule 
        which can also be generalized two different ways using list implication. *}

lemma (in Minimal_Logic) flip_implication: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> \<psi> \<rightarrow> \<phi> \<rightarrow> \<chi>"  
  by (meson Axiom_1 Axiom_2 Modus_Ponens) 

lemma (in Minimal_Logic) list_flip_implication1: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N (\<phi> # \<Gamma>) :\<rightarrow> \<chi> \<rightarrow> \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<chi>)"
  by (induct \<Gamma>, 
      (simp, meson Axiom_1 Axiom_2 Modus_Ponens flip_implication hypothetical_syllogism)+)    
    
lemma (in Minimal_Logic) list_flip_implication2: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> # \<Gamma>) :\<rightarrow> \<chi>"
  by (induct \<Gamma>, 
      (simp, meson Axiom_1 Axiom_2 Modus_Ponens flip_implication hypothetical_syllogism)+)    

text {* The lemma @{thm "list_flip_implication2"} presents a means of \emph{introducing}
        assumptions into a list of assumptions when those assumptions have arrived at an implication.  
        The next lemma presents a means of \emph{discharging} those assumptions. *}

lemma (in Minimal_Logic) implication_absorption: "\<turnstile>\<^sub>M\<^sub>I\<^sub>N (\<phi> \<rightarrow> \<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"  
  by (meson Axiom_1 Axiom_2 Modus_Ponens)  
  
lemma (in Minimal_Logic) list_implication_removeAll:
  "\<turnstile>\<^sub>M\<^sub>I\<^sub>N \<Gamma> :\<rightarrow> \<psi> \<rightarrow> (removeAll \<phi> \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
proof(induct \<Gamma>)
  case Nil
  then show ?case by (simp, meson Axiom_1)
next
  case (Cons \<chi> \<Gamma>)
  then show ?case apply(simp) 
qed
  
