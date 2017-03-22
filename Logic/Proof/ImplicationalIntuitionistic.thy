section \<open>The Implicational Fragment of Intuitionistic Logic\<close>
  
theory ImplicationalIntuitionistic
imports Main "../Formula" "../../Functional/Combinator/Simply_Typed_Free_SKCombinator"
begin

text \<open>This theory presents the implicational fragment of intuitionistic logic.\<close>

subsection \<open>Axiomatization\<close>

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
      This is achieved by establishing the \emph{Curry-Howard correspondence}\<close>
    
lemma curry_howard_elimination: "c \<Colon> \<phi> \<Longrightarrow> \<turnstile>\<^sub>I\<^sub>I\<^sub>L \<phi>"
proof (induct rule: Simply_Typed_Free_SKCombinator.induct)
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
    
datatype 'x Lambda = 
    Var 'x                         ("\<langle>_\<rangle>" [100] 100)
  | Lambda 'x "'x Lambda"          ("\<^bold>\<lambda> _. _" [90,90] 90)
  | Apply "'x Lambda" "'x Lambda"  (infixl "\<cdot>" 85)

datatype 'x Variable_SKCombinator =
    Var' 'x                           ("\<guillemotleft>_\<guillemotright>" [100] 100)
  | S'
  | K'
  | Apply "'x Variable_SKCombinator"
          "'x Variable_SKCombinator" (infixl "\<odot>" 75) 

fun to_Free_SKCombinator :: "'x Variable_SKCombinator \<Rightarrow> Free_SKCombinator" ("\<lbrace>_\<rbrace>" [72] 72)
  where
      "\<lbrace>S'\<rbrace> = S"
    | "\<lbrace>K'\<rbrace> = K"
    | "\<lbrace>E\<^sub>1 \<odot> E\<^sub>2\<rbrace> = \<lbrace>E\<^sub>1\<rbrace> \<bullet> \<lbrace>E\<^sub>2\<rbrace>"
    | "\<lbrace>_\<rbrace> = undefined"

definition I :: "'x Variable_SKCombinator" where "I \<equiv> S' \<odot> K' \<odot> K'"

lemma I_type: "\<lbrace>I\<rbrace> \<Colon> \<phi> \<rightarrow> \<phi>"
  by (metis Simply_Typed_Free_SKCombinator.simps 
            I_def 
            to_Free_SKCombinator.simps(1) 
            to_Free_SKCombinator.simps(2) 
            to_Free_SKCombinator.simps(3))       
      
fun free_variables_in_lambda :: "'x Lambda \<Rightarrow> 'x set" ("free\<^sub>\<lambda>")
  where
      "free\<^sub>\<lambda> (\<langle>x\<rangle>) = {x}"
    | "free\<^sub>\<lambda> (\<^bold>\<lambda> x. E) = free\<^sub>\<lambda> E - {x}"
    | "free\<^sub>\<lambda> (E\<^sub>1 \<cdot> E\<^sub>2) = free\<^sub>\<lambda> E\<^sub>1 \<union> free\<^sub>\<lambda> E\<^sub>2"

fun free_variables_in_SKCombinator :: "'x Variable_SKCombinator \<Rightarrow> 'x set" ("free\<^sub>S\<^sub>K")
  where
    "free\<^sub>S\<^sub>K (\<guillemotleft>x\<guillemotright>) = {x}"
  | "free\<^sub>S\<^sub>K S' = {}"
  | "free\<^sub>S\<^sub>K K' = {}"    
  | "free\<^sub>S\<^sub>K (E\<^sub>1 \<odot> E\<^sub>2) = free\<^sub>S\<^sub>K E\<^sub>1 \<union> free\<^sub>S\<^sub>K E\<^sub>2"
    
fun schoenfinkle_embedding :: "'x Lambda \<Rightarrow> 'x Variable_SKCombinator" ("\<lparr>_\<rparr>" [80] 80) 
  where
    "\<lparr>\<^bold>\<lambda> x. \<langle>y\<rangle>\<rparr> = (if (x = y) then I else undefined)"
  | "\<lparr>A \<cdot> B\<rparr> = (\<lparr>A\<rparr> \<odot> \<lparr>B\<rparr>)" 
  | "\<lparr>_\<rparr> = undefined"    
    
end
