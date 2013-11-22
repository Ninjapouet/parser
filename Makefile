pkgs:=pkgs
packages:=$(shell find $(pkgs) -mindepth 1 -maxdepth 1 -type d)
ocamlbuild:=ocamlbuild $(foreach p,$(packages),-I $(p)/src)

all:
	$(ocamlbuild) src/parser.byte
