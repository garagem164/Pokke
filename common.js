// ---- funções copiadas de lz77.js / romHeader.js / species.js ----
// (mesma implementação, adaptada pra rodar direto no navegador sem bundler)

function lz77Decompress(data, offset) {
  const type = data[offset];
  if (type !== 0x10) {
    throw new Error(`Offset 0x${offset.toString(16)} não é um bloco LZ77 (tipo=0x${type.toString(16)})`);
  }
  const size = data[offset + 1] | (data[offset + 2] << 8) | (data[offset + 3] << 16);
  const out = new Uint8Array(size);
  let outPos = 0, pos = offset + 4;
  while (outPos < size) {
    const flags = data[pos++];
    for (let bit = 7; bit >= 0 && outPos < size; bit--) {
      if ((flags >> bit) & 1) {
        const b1 = data[pos++], b2 = data[pos++];
        const length = (b1 >> 4) + 3;
        const disp = (((b1 & 0x0f) << 8) | b2) + 1;
        for (let i = 0; i < length && outPos < size; i++) { out[outPos] = out[outPos - disp]; outPos++; }
      } else {
        out[outPos++] = data[pos++];
      }
    }
  }
  return { bytes: out, nextOffset: pos };
}

function bytesToAscii(data, offset, length) {
  let s = "";
  for (let i = 0; i < length; i++) { const b = data[offset + i]; if (b === 0) break; s += String.fromCharCode(b); }
  return s;
}

function parseRomHeader(data) {
  const title = bytesToAscii(data, 0xa0, 12).trim();
  const gameCode = bytesToAscii(data, 0xac, 4);
  const makerCode = bytesToAscii(data, 0xb0, 2);
  const version = data[0xbc];
  return { title, gameCode, makerCode, version, key: `${gameCode}${version}` };
}

const KNOWN_GAME_CODES = {
  BPRE: "Pokémon Fire Red (EN)", BPGE: "Pokémon Leaf Green (EN)",
  BPRJ: "Pokémon Fire Red (JP)", BPGJ: "Pokémon Leaf Green (JP)",
};

const KNOWN_OFFSETS = {
  BPRE0: { baseStats: 0x254784 },
  BPGE0: { baseStats: 0x254784 },
};

const TYPE_NAMES = ["Normal","Lutador","Voador","Venenoso","Terra","Pedra","Inseto","Fantasma","Aço","???","Fogo","Água","Planta","Elétrico","Psíquico","Gelo","Dragão","Sombrio"];
const ENTRY_SIZE = 28;

function readSpecies(data, baseStatsOffset, speciesIndex) {
  const off = baseStatsOffset + speciesIndex * ENTRY_SIZE;
  return {
    hp: data[off+0], attack: data[off+1], defense: data[off+2], speed: data[off+3],
    spAttack: data[off+4], spDefense: data[off+5],
    type1: TYPE_NAMES[data[off+6]] ?? `?(${data[off+6]})`,
    type2: TYPE_NAMES[data[off+7]] ?? `?(${data[off+7]})`,
    catchRate: data[off+8], expYield: data[off+9],
  };
}

const BULBASAUR_EXPECTED = { hp:45, attack:49, defense:49, speed:45, spAttack:65, spDefense:65, type1:"Planta", type2:"Venenoso" };

function validateBulbasaur(data, baseStatsOffset) {
  const read = readSpecies(data, baseStatsOffset, 1);
  const mismatches = Object.keys(BULBASAUR_EXPECTED).filter(f => read[f] !== BULBASAUR_EXPECTED[f]);
  return { ok: mismatches.length === 0, read, expected: BULBASAUR_EXPECTED, mismatches };
}

// ---- leitor de ZIP mínimo (sem dependências) ----
function readU32LE(data, o) { return (data[o] | (data[o+1]<<8) | (data[o+2]<<16) | (data[o+3]<<24)) >>> 0; }
function readU16LE(data, o) { return data[o] | (data[o+1]<<8); }
function isZip(data) { return data.length >= 4 && readU32LE(data,0) === 0x04034b50; }

function listZipEntries(data) {
  let eocdOffset = -1;
  for (let i = data.length - 22; i >= 0; i--) {
    if (readU32LE(data, i) === 0x06054b50) { eocdOffset = i; break; }
  }
  if (eocdOffset === -1) throw new Error("Não encontrei o fim do diretório central do ZIP — arquivo corrompido ou incompleto.");
  const totalEntries = readU16LE(data, eocdOffset + 10);
  const centralDirOffset = readU32LE(data, eocdOffset + 16);
  const entries = [];
  let p = centralDirOffset;
  for (let i = 0; i < totalEntries; i++) {
    if (readU32LE(data, p) !== 0x02014b50) throw new Error("Diretório central do ZIP corrompido.");
    const compressionMethod = readU16LE(data, p + 10);
    const compressedSize = readU32LE(data, p + 20);
    const filenameLen = readU16LE(data, p + 28);
    const extraLen = readU16LE(data, p + 30);
    const commentLen = readU16LE(data, p + 32);
    const localHeaderOffset = readU32LE(data, p + 42);
    let filename = "";
    for (let j = 0; j < filenameLen; j++) filename += String.fromCharCode(data[p + 46 + j]);
    entries.push({ filename, compressionMethod, compressedSize, localHeaderOffset });
    p += 46 + filenameLen + extraLen + commentLen;
  }
  return entries;
}

function getCompressedEntryData(data, entry) {
  const p = entry.localHeaderOffset;
  if (readU32LE(data, p) !== 0x04034b50) throw new Error(`Cabeçalho local inválido pra "${entry.filename}"`);
  const filenameLen = readU16LE(data, p + 26);
  const extraLen = readU16LE(data, p + 28);
  const dataStart = p + 30 + filenameLen + extraLen;
  return data.subarray(dataStart, dataStart + entry.compressedSize);
}

async function inflateRawBrowser(compressed) {
  const ds = new DecompressionStream("deflate-raw");
  const stream = new Blob([compressed]).stream().pipeThrough(ds);
  const buf = await new Response(stream).arrayBuffer();
  return new Uint8Array(buf);
}

// ---- versão "estrita" do LZ77, usada só pra escanear a ROM em busca
// de blocos válidos: detecta e rejeita falsos positivos (bytes que
// por acaso começam com 0x10 mas não são um bloco LZ77 de verdade),
// em vez de ler lixo silenciosamente.
function lz77DecompressStrict(data, offset, maxSize) {
  const type = data[offset];
  if (type !== 0x10) throw new Error("não é LZ77");
  const size = data[offset + 1] | (data[offset + 2] << 8) | (data[offset + 3] << 16);
  if (size === 0 || size > maxSize) throw new Error("tamanho implausível");

  const out = new Uint8Array(size);
  let outPos = 0, pos = offset + 4;

  while (outPos < size) {
    if (pos >= data.length) throw new Error("passou do fim do arquivo");
    const flags = data[pos++];
    for (let bit = 7; bit >= 0 && outPos < size; bit--) {
      if (pos >= data.length) throw new Error("passou do fim do arquivo");
      if ((flags >> bit) & 1) {
        const b1 = data[pos++], b2 = data[pos++];
        const length = (b1 >> 4) + 3;
        const disp = (((b1 & 0x0f) << 8) | b2) + 1;
        if (disp > outPos) throw new Error("referência inválida (fluxo corrompido)");
        for (let i = 0; i < length && outPos < size; i++) { out[outPos] = out[outPos - disp]; outPos++; }
      } else {
        out[outPos++] = data[pos++];
      }
    }
  }
  return { bytes: out, nextOffset: pos };
}

/**
 * Escaneia a ROM inteira procurando blocos LZ77 que descomprimem pra
 * um tamanho exato (ex: 2048 bytes = sprite 64x64px em 4bpp).
 * Usado quando não sabemos o offset da tabela de sprites de antemão.
 */
function scanForCompressedBlocks(data, targetSize, maxResults, onProgress) {
  const results = [];
  const total = data.length;
  for (let i = 0; i < total - 4 && results.length < maxResults; i++) {
    if (data[i] !== 0x10) continue;
    const size = data[i + 1] | (data[i + 2] << 8) | (data[i + 3] << 16);
    if (size !== targetSize) continue;
    try {
      const { bytes } = lz77DecompressStrict(data, i, targetSize);
      results.push({ offset: i, bytes });
    } catch (e) {
      // falso positivo (byte 0x10 por coincidência) — ignora
    }
    if (onProgress && i % 500000 === 0) onProgress(i / total);
  }
  return results;
}

/**
 * Renderiza um bloco de tiles 4bpp do GBA (8x8px cada) numa grade
 * quadrada, usando escala de cinza (sem paleta real ainda — serve
 * pra reconhecer a FORMA do sprite visualmente).
 * bytes.length deve ser um múltiplo de 32 (1 tile = 32 bytes).
 */
function render4bppGrayscale(bytes, canvas) {
  const tileCount = bytes.length / 32;
  const tilesPerRow = Math.round(Math.sqrt(tileCount));
  const size = tilesPerRow * 8;
  canvas.width = size;
  canvas.height = size;
  const ctx = canvas.getContext("2d");
  const img = ctx.createImageData(size, size);

  for (let t = 0; t < tileCount; t++) {
    const tileX = (t % tilesPerRow) * 8;
    const tileY = Math.floor(t / tilesPerRow) * 8;
    const tileOffset = t * 32;
    for (let row = 0; row < 8; row++) {
      for (let col = 0; col < 4; col++) {
        const byte = bytes[tileOffset + row * 4 + col];
        const left = byte & 0x0f;
        const right = (byte >> 4) & 0x0f;
        for (const [px, val] of [[col * 2, left], [col * 2 + 1, right]]) {
          const x = tileX + px, y = tileY + row;
          const idx = (y * size + x) * 4;
          const shade = val * 17; // 0..15 -> 0..255
          img.data[idx] = shade;
          img.data[idx + 1] = shade;
          img.data[idx + 2] = shade;
          img.data[idx + 3] = val === 0 ? 0 : 255; // índice 0 = transparente
        }
      }
    }
  }
  ctx.putImageData(img, 0, 0);
}

/**
 * Carrega um arquivo de ROM (.gba ou .zip), extrai se necessário, e
 * valida o cabeçalho. Retorna { data, header } ou null se inválido
 * (já loga o motivo usando a função `log` passada).
 */
async function loadRomFile(file, log) {
  const buffer = await file.arrayBuffer();
  let data = new Uint8Array(buffer);

  if (isZip(data)) {
    log(`"${file.name}" é um ZIP. Procurando .gba lá dentro...`);
    try {
      const extracted = await extractFileByExtension(data, [".gba"]);
      log(`<span class="ok">✔ Extraído: "${extracted.filename}" (${(extracted.bytes.length/1024/1024).toFixed(2)} MB)</span>`);
      data = extracted.bytes;
    } catch (err) {
      log(`<span class="fail">✘ Erro ao extrair o zip: ${err.message}</span>`);
      return null;
    }
  }

  const fixedByte = data[0xb2];
  if (fixedByte !== 0x96) {
    log(`<span class="fail">✘ Byte fixo do cabeçalho inválido (0x${fixedByte.toString(16)}, esperado 0x96). Não é uma ROM de GBA válida.</span>`);
    return null;
  }

  const header = parseRomHeader(data);
  log(`<span class="ok">✔ ${header.title} — ${header.gameCode} rev ${header.version} (${header.key})</span>`);
  return { data, header };
}

async function extractFileByExtension(data, extensions) {
  const entries = listZipEntries(data);
  const match = entries.find((e) => extensions.some((ext) => e.filename.toLowerCase().endsWith(ext)));
  if (!match) {
    const names = entries.map((e) => e.filename).join(", ") || "(zip vazio)";
    throw new Error(`Não achei nenhum arquivo ${extensions.join("/")} dentro do zip. Encontrados: ${names}`);
  }
  const compressed = getCompressedEntryData(data, match);
  let bytes;
  if (match.compressionMethod === 0) bytes = compressed;
  else if (match.compressionMethod === 8) bytes = await inflateRawBrowser(compressed);
  else throw new Error(`Método de compressão não suportado (código ${match.compressionMethod}) pra "${match.filename}"`);
  return { filename: match.filename, bytes };
}

