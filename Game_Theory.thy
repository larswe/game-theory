theory Game_Theory 
  imports "HOL-Analysis.Analysis"
begin

locale strategic_game = 
  fixes number_of_players :: "nat"
begin

abbreviation "n == number_of_players"

definition players :: "nat set" where "players = {i :: nat . (1 :: nat) \<le> i \<and> i \<le> n}"




end

end