import requests
import gzip
import os
import xml.etree.ElementTree as ET
import io
# URL dei file GZIP o XML da elaborare
URLS_GZIP = [
    'https://www.open-epg.com/files/italy1.xml',
    'https://www.open-epg.com/files/italy2.xml',
    'https://www.open-epg.com/files/italy3.xml',
    'https://www.open-epg.com/files/italy4.xml'
]
# File di output finale
OUTPUT_XML_FINAL = 'epg.xml'
# URL remoto di it.xml (PlutoTV)
URL_IT_XML = 'https://raw.githubusercontent.com/matthuisman/i.mjh.nz/master/PlutoTV/it.xml'
# File eventi locale (input per questo script)
PATH_EVENTI_INPUT = 'eventi.xml'
def download_and_parse_xml(url):
    """Scarica un file .xml o .gzip e restituisce l'ElementTree."""
    print(f"  Tentativo di scaricare e parsare: {url}")
    try:
        response = requests.get(url, timeout=30)
        response.raise_for_status()
        # Prova a decomprimere come GZIP
        try:
            with gzip.open(io.BytesIO(response.content), 'rb') as f_in:
                xml_content = f_in.read()
            print(f"    -> Decompresso come GZIP.")
        except (gzip.BadGzipFile, OSError):
            # Non è un file gzip, usa direttamente il contenuto
            xml_content = response.content
            print(f"    -> Letto come XML semplice.")
        return ET.ElementTree(ET.fromstring(xml_content))
    except requests.exceptions.RequestException as e:
        print(f"    ERRORE durante il download da {url}: {e}")
    except ET.ParseError as e:
        print(f"    ERRORE nel parsing del file XML da {url}: {e}")
    return None
def clean_attribute(element, attr_name):
    """
    Pulisce un attributo specifico di un elemento XML:
    rimuove gli spazi e converte in minuscolo.
    """
    if attr_name in element.attrib:
        old_value = element.attrib[attr_name]
        new_value = old_value.replace(" ", "").lower()
        if old_value != new_value:
            # print(f"    Attributo '{attr_name}' pulito: '{old_value}' -> '{new_value}'")
            element.attrib[attr_name] = new_value
def merge_epg_data():
    """Funzione principale per unire i dati EPG da varie fonti."""
    print("Avvio del processo di unione EPG...")
    root_finale = ET.Element('tv')
    tree_finale = ET.ElementTree(root_finale)
    # Processare ogni URL GZIP da open-epg.com
    print("\nElaborazione degli URL GZIP da open-epg.com...")
    for url in URLS_GZIP:
        tree = download_and_parse_xml(url)
        if tree is not None:
            root = tree.getroot()
            for element in root:  # Aggiunge tutti gli elementi principali (canali e programmi)
                root_finale.append(element)
            print(f"    -> Dati da {url} aggiunti con successo.")
        else:
            print(f"    -> Fallimento nell'elaborazione di {url}.")
    # Aggiungere programmi da eventi.xml (file locale)
    print(f"\nElaborazione dei programmi dal file locale: {PATH_EVENTI_INPUT}...")
    if os.path.exists(PATH_EVENTI_INPUT):
        try:
            tree_eventi = ET.parse(PATH_EVENTI_INPUT)
            root_eventi = tree_eventi.getroot()
            program_count = 0
            for programme in root_eventi.findall(".//programme"):  # Aggiunge solo i programmi
                root_finale.append(programme)
                program_count += 1
            print(f"  -> {program_count} programmi da {PATH_EVENTI_INPUT} aggiunti con successo.")
        except ET.ParseError as e:
            print(f"  ERRORE nel parsing del file {PATH_EVENTI_INPUT}: {e}")
    else:
        print(f"  ATTENZIONE: File non trovato: {PATH_EVENTI_INPUT}")
    # Aggiungere programmi da it.xml (URL remoto PlutoTV)
    print(f"\nElaborazione dei programmi da PlutoTV (remoto): {URL_IT_XML}...")
    tree_it = download_and_parse_xml(URL_IT_XML)
    if tree_it is not None:
        root_it = tree_it.getroot()
        program_count = 0
        for programme in root_it.findall(".//programme"):  # Aggiunge solo i programmi
            root_finale.append(programme)
            program_count +=1
        print(f"  -> {program_count} programmi da {URL_IT_XML} aggiunti con successo.")
    else:
        print(f"  Fallimento nell'elaborazione di {URL_IT_XML}.")
    # Pulire gli ID dei canali (questi canali dovrebbero provenire principalmente da urls_gzip)
    print("\nPulizia degli ID dei canali...")
    channel_cleaned_count = 0
    for channel in root_finale.findall(".//channel"):
        clean_attribute(channel, 'id')
        channel_cleaned_count +=1
    print(f"  -> ID puliti per {channel_cleaned_count} canali.")
    # Pulire gli attributi 'channel' nei programmi
    print("\nPulizia degli attributi 'channel' nei programmi...")
    programme_channel_cleaned_count = 0
    for programme in root_finale.findall(".//programme"):
        clean_attribute(programme, 'channel')
        programme_channel_cleaned_count +=1
    print(f"  -> Attributi 'channel' puliti per {programme_channel_cleaned_count} programmi.")
    # Salvare il file XML finale
    print(f"\nSalvataggio del file XML finale in: {OUTPUT_XML_FINAL}...")
    try:
        with open(OUTPUT_XML_FINAL, 'wb') as f_out: # 'wb' per scrivere bytes (necessario per xml_declaration)
            tree_finale.write(f_out, encoding='utf-8', xml_declaration=True)
        print(f"✅ File XML combinato salvato con successo in: {OUTPUT_XML_FINAL}")
    except IOError as e:
        print(f"ERRORE: Impossibile scrivere il file EPG finale '{OUTPUT_XML_FINAL}': {e}")
    except Exception as e:
        print(f"ERRORE: Si è verificato un errore imprevisto durante il salvataggio del file EPG: {e}")
if __name__ == "__main__":
    # Assicurati che lo script sia eseguito dalla directory corretta
    # o che i percorsi ai file locali (PATH_EVENTI_INPUT) siano assoluti
    # o relativi alla posizione di esecuzione dello script.
    script_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(script_dir) # Cambia la directory di lavoro corrente a quella dello script
    print(f"Directory di lavoro impostata su: {script_dir}")
    
    merge_epg_data()