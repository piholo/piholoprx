import sys
import os
import requests  # Aggiungiamo questa libreria per gestire le richieste HTTP

def merge_m3u8_lists(input_files, output_file="listone.m3u8", remote_urls=None):
    """
    Unisce più file M3U8 in un singolo file.
    Mantiene la prima riga #EXTM3U solo dal primo file di input.

    Args:
        input_files (list): Una lista di percorsi ai file M3U8 da unire.
        output_file (str): Il nome del file di output.
        remote_urls (list): Una lista di URL remoti di file M3U8 da unire.
    """
    if not input_files and not remote_urls:
        print("Errore: Nessun file di input o URL remoto specificato.")
        print("Utilizzo: python3 mergelists.py file1.m3u8 file2.m3u8 ... --remote url1 url2 ...")
        return

    # Stampa informazioni sui file da unire
    files_info = ", ".join(input_files) if input_files else ""
    if remote_urls:
        if files_info:
            files_info += ", "
        files_info += ", ".join(remote_urls)
    print(f"Unione dei file: {files_info} in {output_file}")

    try:
        with open(output_file, 'w', encoding='utf-8') as outfile:
            first_file = True

            # Processa i file locali
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

                    print(f"Processato file locale: {input_file}")

                except Exception as e:
                    print(f"Errore durante la lettura del file {input_file}: {e}")

            # Processa gli URL remoti
            if remote_urls:
                for url in remote_urls:
                    try:
                        print(f"Scaricamento della playlist da {url}...")
                        response = requests.get(url, timeout=10)
                        response.raise_for_status()  # Solleva un'eccezione per errori HTTP
                        content = response.text

                        # Dividi il contenuto in righe
                        lines = content.splitlines()

                        # Salta la prima riga se è #EXTM3U e non è il primo file
                        if lines and lines[0].strip().startswith('#EXTM3U'):
                            if first_file:
                                outfile.write(lines[0] + '\n')
                                first_file = False
                                lines = lines[1:]
                            else:
                                lines = lines[1:]

                        # Scrivi il resto delle righe
                        for line in lines:
                            outfile.write(line + '\n')

                        print(f"Processato URL remoto: {url}")

                    except Exception as e:
                        print(f"Errore durante il download o l'elaborazione dell'URL {url}: {e}")

    except Exception as e:
        print(f"Errore durante la scrittura del file di output {output_file}: {e}")

    print("Processo di unione completato.")

if __name__ == "__main__":
    # Analizza gli argomenti della riga di comando
    input_files = []
    remote_urls = []

    i = 1
    while i < len(sys.argv):
        if sys.argv[i] == "--remote":
            # Tutti gli argomenti successivi sono URL remoti
            remote_urls = sys.argv[i+1:]
            break
        else:
            input_files.append(sys.argv[i])
        i += 1

    # Se non ci sono URL remoti specificati, aggiungi l'URL di Pluto TV
    if not remote_urls:
        remote_urls = ["https://raw.githubusercontent.com/Brenders/Pluto-TV-Italia-M3U/main/PlutoItaly.m3u"]

    merge_m3u8_lists(input_files, remote_urls=remote_urls)
