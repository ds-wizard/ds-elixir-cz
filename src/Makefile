all: Main.hs
	hastec Main.hs -o ../Server/static/js/main.js -Wall --debug

production: Main.hs
	hastec Main.hs -o ../Server/static/js/main.js -Wall --opt-all

clean:
	find -L . -name "*.o" -exec rm -rf {} \;
	find -L . -name "*.hi" -exec rm -rf {} \;
	find -L . -name "*.jsmod" -exec rm -rf {} \;