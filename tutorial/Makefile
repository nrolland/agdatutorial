
DOTS=$(wildcard dot/*.dot)
DOTPNG=$(patsubst dot/%.dot, html/dot/%.gif, $(DOTS))

.PHONY: html sync clean

html: $(DOTPNG)
	agdapandoc -i ~/share/Agda/lib/src/ -i src --html=NoSlides src/Index.lagda --css=Agda.css
#	agda -i ~/share/Agda/lib/src/ -i . --html=SlidySlides --template=slidy.template Index.lagda --css=Agda.css
#	agda -i ~/share/Agda/lib/src/ -i . --html=S5Slides --template=s5.template Index.lagda --css=Agda.css
#	agda -i ~/share/Agda/lib/src/ -i . --html=DZSlides --template=dz.template Index.lagda --css=Agda.css
#	agda -i ~/share/Agda/lib/src/ -i . --html=SlideousSlides --template=slideous.template Index.lagda --css=Agda.css

clean:
	find . -name "*.agdai" -exec rm -f {} \; 
	find . -name "*~" -exec rm -f {} \; 
	rm -f html/dot/*
	rm -f html/*.html

html/dot/%.gif: dot/%.dot
	dot -Tgif $< -o $@

