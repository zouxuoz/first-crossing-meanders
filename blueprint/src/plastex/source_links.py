"""Link this frozen artifact's declarations to their Lean-reported source locations."""
import json
from pathlib import Path


SOURCE_REVISION = '7eaeaf5834295b09dca5402fb57e8843e322ac11'

def ProcessOptions(options, document):
    def source_links():
        root = Path(document.userdata['working-dir']).parents[1]
        locations = json.loads((root / 'blueprint/source-links.json').read_text())
        repository = document.userdata['project_github']
        for graph in document.userdata['dep_graph']['graphs'].values():
            for node in graph.nodes:
                links = []
                for name in node.userdata.get('leandecls', []):
                    location = locations[name]
                    path, line = location['path'], location['line']
                    if not (root / path).is_file():
                        raise ValueError(f'Missing Lean source for {name}: {path}')
                    links.append((name, f'{repository}/blob/{SOURCE_REVISION}/{path}#L{line}'))
                node.userdata['lean_urls'] = links
    document.addPostParseCallbacks(160, source_links)
