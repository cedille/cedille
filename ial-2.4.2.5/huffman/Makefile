LIBS = -i . -i ~/ial -i ~/gratr2/agda

main:	main.agda huffman-tree.agda huffman-main.agda
	agda -v 0 $(LIBS) -c main.agda

huffman-main:	huffman-main.agda
	agda -v 0 $(LIBS) -c huffman-main.agda

huffman-main.agda:	huffman.gr
	gratr huffman.gr
