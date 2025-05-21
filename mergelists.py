import sys
import os

def merge_m3u8_lists(input_files, output_file="listone.m3u8"):
    """
    Unisce più file M3U8 in un singolo file.
    Mantiene la prima riga #EXTM3U solo dal primo file di input.

    Args:
        input_files (list): Una lista di percorsi ai file M3U8 da unire.
        output_file (str): Il nome del file di output.
    """
    if not input_files:
        print("Errore: Nessun file di input specificato.")
        print("Utilizzo: python3 mergelists.py file1.m3u8 file2.m3u8 ...")
        return

    print(f"Unione dei file: {', '.join(input_files)} in {output_file}")

    try:
        with open(output_file, 'w', encoding='utf-8') as outfile:
            first_file = True
            for input_file in input_files:
                if not os.path.exists(input_file):
                    print(f"Avviso: File non trovato - {input_file}. Saltato.")
                    continue

                try:
                    with open(input_file, 'r', encoding='utf-8') as infile:
                        # Leggi la prima riga separatamente
                        first_line = infile.readline()

                        if first_file:
                            # Scrivi la prima riga (inclusa la direttiva #EXTM3U) solo per il primo file
                            outfile.write(first_line)
                            first_file = False
                        else:
                            # Per i file successivi, salta la prima riga se è una direttiva #EXTM3U
                            # Altrimenti, scrivi la prima riga se non inizia con #EXTM3U
                            if not first_line.strip().startswith('#EXTM3U'):
                                outfile.write(first_line)

                        # Scrivi il resto delle righe
                        for line in infile:
                            outfile.write(line)

                    print(f"Processato: {input_file}")

                except Exception as e:
                    print(f"Errore durante la lettura del file {input_file}: {e}")

    except Exception as e:
        print(f"Errore durante la scrittura del file di output {output_file}: {e}")

    print("Processo di unione completato.")

if __name__ == "__main__":
    # sys.argv[0] è il nome dello script, quindi i file iniziano da sys.argv[1]
    input_files = sys.argv[1:]
    merge_m3u8_lists(input_files)
