all: app/Main.hs
	stack build

configure:
	stack clean --full
	stack setup

clean:
	stack clean
	find -L . -name "*.swp" -exec rm -rf {} \;

run: all
	stack exec Elixir-cz-fairdata-solutions
