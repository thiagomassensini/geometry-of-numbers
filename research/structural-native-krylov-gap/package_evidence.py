from pathlib import Path
import gzip,hashlib,json
folder=Path(__file__).resolve().parent;evidence=folder/'evidence'
p=evidence/'validation.json';r=json.loads(p.read_text())
assert len(r['checks'])==10 and all(c['exit_code']==0 for c in r['checks'])
for f in evidence.glob('*.log'):
    q=f.with_suffix('.log.gz');q.write_bytes(gzip.compress(f.read_bytes(),mtime=0));f.unlink()
for c in r['checks']:
    if not c['log'].endswith('.gz'):
        c['uncompressed_sha256']=c['sha256'];c['log']+='.gz'
        c['sha256']=hashlib.sha256((evidence/c['log']).read_bytes()).hexdigest()
p.write_text(json.dumps(r,indent=2)+'\n')
s='# Validação final\n\n| Comando | Saída | Log |\n| --- | --- | --- |\n'
for c in r['checks']:
    s+='| `'+ ' '.join(c['command']) +'` | '+str(c['exit_code'])+' | `evidence/'+c['log']+'` |\n'
s+='\nAuditoria nova: 9 raízes de biblioteca / 4649 declarações transitivas; 13 raízes de pesquisa / 5719 declarações transitivas. Todos os 22 teoremas passaram o guard e `#print axioms`; apenas os três axiomas padrão permitidos.\n\nOs jobs Lake incluem replay de dependências já compiladas. A compilação cruzada explícita usa o ambiente original e caches das pesquisas certificadas. Não foram alterados pins. Para reconstruir caches históricos ausentes, usar os validadores preexistentes de `research/sixth-odd-twelve-sources/` e seus pré-requisitos antes do `validate.py` desta rodada.\n\nO CSV de preflight é apenas diagnóstico de decimais armazenados; os teoremas Lean usam caixas dos integrais theta já certificados. Hashes das fontes e logs estão nos manifestos, e `verify_evidence.py` os confere.\n'
(folder/'VALIDATION.md').write_text(s)
