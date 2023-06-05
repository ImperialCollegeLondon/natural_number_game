rm -rf html/
rm -f src/game/**/*.olean
make-lean-game

cp src/game/LaTeX/implies_diag.jpg src/game/LaTeX/function_diag.jpg src/game/LaTeX/FAQ.html html/
