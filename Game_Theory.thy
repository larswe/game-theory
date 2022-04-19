theory Game_Theory 
  imports "HOL-Analysis.Analysis"
begin

section "Defining a Simultaneous Move Game"

locale strategic_game = 
  fixes possible_strategies :: "'player :: finite  \<Rightarrow> 'strategy set"
    and payoffs :: "('strategy, 'player) vec \<Rightarrow> ('payoff :: linorder, 'player) vec"
begin

text "Strategy selection"
(* TODO - This should be a bit more precise. *)
definition strategy_maps 
  where "strategy_maps = {f :: 'player \<Rightarrow> 'strategy. \<forall>i. f i \<in> possible_strategies i}"

definition strategy_vector :: "('player \<Rightarrow> 'strategy) \<Rightarrow> ('strategy, 'player) vec" 
  where "strategy_vector f = (\<chi> i. f i)"

definition strategy_vectors 
  where "strategy_vectors = {s. \<exists>f. (s = strategy_vector f \<and> f \<in> strategy_maps)}"

definition payoff :: "('strategy, 'player) vec \<Rightarrow> 'player \<Rightarrow> 'payoff" 
  where "payoff s i = (payoffs s)$i"

end

text "Strategic form games with real-valued payoffs."
locale real_out_strategic_game = strategic_game possible_strategies payoffs
  for payoffs :: "('strategy, 'player) vec \<Rightarrow> (real, 'player :: finite) vec"
  and possible_strategies
begin

text "For real-valued payoffs, costs can be defined to be their additive inverse."
definition costs :: "('strategy, 'player) vec \<Rightarrow> (real, 'player) vec"
  where "costs s = -(payoffs s)"

definition cost :: "('strategy, 'player) vec \<Rightarrow> 'player \<Rightarrow> real"
  where "cost s i = (costs s)$i"

lemma cost_neg_pay: 
  shows "cost s i = -(payoff s i)"
  by (simp add: cost_def costs_def payoff_def)

end

end