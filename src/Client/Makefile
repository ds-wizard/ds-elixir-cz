all: Main.hs
	hastec Main.hs -o ../../static/js/main.js -Wall --debug 

production: Main.hs
	hastec Main.hs -o Page/js/main.js -Wall 

clean: 
	find . -name "*.o" -exec rm -rf {} \; 
	find . -name "*.hi" -exec rm -rf {} \; 
	find . -name "*.jsmod" -exec rm -rf {} \; 