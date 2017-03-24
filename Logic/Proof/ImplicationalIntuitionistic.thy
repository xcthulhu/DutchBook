section \<open>The Implicational Fragment of Intuitionistic Logic\<close>
  
theory ImplicationalIntuitionistic
  imports "../Formula" 
          "../../Functional/SKCombinator"
begin

text \<open>This theory presents the implicational fragment of intuitionistic logic.\<close>

subsection \<open>Axiomatization\<close>

text \<open>The implicational fragment of intuitionistic logic is given via a simple 
      Hilbert-style axiom system:\<close>
  
inductive iil_proof :: "'a Formula \<Rightarrow> bool" ("\<turnstile>\<^sub>I\<^sub>I\<^sub>L _" [60] 55)
  where
    S_axiom      : "\<turnstile>\<^sub>I\<^sub>I\<^sub>L (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  | K_axiom      : "\<turnstile>\<^sub>I\<^sub>I\<^sub>L \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  | modus_ponens : "\<turnstile>\<^sub>I\<^sub>I\<^sub>L \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile>\<^sub>I\<^sub>I\<^sub>L \<phi> \<Longrightarrow> \<turnstile>\<^sub>I\<^sub>I\<^sub>L \<psi>"

text \<open>Note: since @{term \<bottom>} is a @{typ "'a Formula"}, it is natural to expect the above 
      axiomatization to obey \empy{ex falso quodlibet}, i.e. @{term "\<turnstile>\<^sub>I\<^sub>I\<^sub>L \<bottom> \<rightarrow> \<phi>"}.\<close>

text \<open>This is not the case.\<close>

text \<open>The purpose of this subsystem is to permit \emph{simply typed} combinators
      to serve as a domain specific language for composing proofs.
      This is achieved by establishing the \emph{Curry-Howard correspondence}.\<close>

text \<open>As such, @{term \<bottom>} is regarded as just another term with no special significance.\<close>  
  
subsection \<open>The Curry Howard Correspondence\<close>

text \<open>While there are a number of formulations of the \emph{Curry Howard Correspondence},
      the formulation presented here relates the implicational fragment of intuitionistic logic
      with the simply typed @{term S} and @{term K} combinators.\<close>
  
text \<open>The (polymorphic) typing for a combinator @{term c} is given by the 
      relation @{term "c \<Colon> \<phi>"}, which is defined in @{theory SKCombinator}.\<close>

text \<open>In practice, only the subsequent elimination lemma is of particular use.\<close>
  
lemma curry_howard_elimination: "c \<Colon> \<phi> \<Longrightarrow> \<turnstile>\<^sub>I\<^sub>I\<^sub>L \<phi>"
proof (induct rule: Simply_Typed_SKCombinator.induct)
  case S_type thus ?case using iil_proof.S_axiom by blast
  next case K_type thus ?case using iil_proof.K_axiom by blast
  next case application thus ?case by (simp add: iil_proof.modus_ponens)
qed

lemma  curry_howard_combinator_exists: "\<turnstile>\<^sub>I\<^sub>I\<^sub>L \<phi> \<Longrightarrow> \<exists> c. c \<Colon> \<phi>" 
proof (induct rule: iil_proof.induct)
  case S_axiom thus ?case using S_type by blast
  next case K_axiom thus ?case using K_type by blast     
  next case modus_ponens thus ?case using application by blast
qed  
  
theorem curry_howard_correspondence: "(\<exists> c. c \<Colon> \<phi>) \<equiv> \<turnstile>\<^sub>I\<^sub>I\<^sub>L \<phi>"
  by (smt curry_howard_combinator_exists curry_howard_elimination)

end
