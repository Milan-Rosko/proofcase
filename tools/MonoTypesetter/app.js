const styles = {
  mobileBorder4: {
    label: "Wrapped for mobile / 4-space left border / 39 wide",
    exampleInput:
      "“Proofcase” is a collection of self-contained Rocq developments. Each component is designed to stand independently, typically as a formal companion to a paper, note, or conceptual construction.",
    formatter: "mobileBorder4",
    settings: {
      totalWidth: 39,
      leftPadding: 4,
    },
  },
  plain75: {
    label: "Plain text / normal / 75 wide",
    exampleInput:
      "This formatter produces plain wrapped text with no surrounding comment box. Paragraphs stay separate, lines are wrapped to width 75, and the right edge remains ragged.",
    formatter: "plain75",
    settings: {
      totalWidth: 75,
      justify: false,
    },
  },
  plainJustified75: {
    label: "Plain text / justified / 75 wide",
    exampleInput:
      "This formatter produces plain wrapped text with no surrounding comment box. Paragraphs stay separate, lines are wrapped to width 75, and interior lines are justified to a straight right edge.",
    formatter: "plainJustified75",
    settings: {
      totalWidth: 75,
      justify: true,
    },
  },
  starredBox75: {
    label: "Justified text / starred box / 75 wide",
    exampleInput:
      "There is no finitely supported row `u` whose one-step Rule 30 image is exactly the centered seed row. A single seeded defect cannot be created in one forward step by a finitely supported predecessor.",
    formatter: "starredBox75",
    settings: {
      totalWidth: 75,
      margin: 4,
      sideLeft: "(*",
      sideRight: "*)",
    },
  },
  centeredBox75: {
    label: "Centered text / starred box / 75 wide",
    exampleInput: "MAIN RESULT",
    formatter: "centeredBox75",
    settings: {
      totalWidth: 75,
      margin: 4,
      sideLeft: "(*",
      sideRight: "*)",
    },
  },
};

const elements = {
  styleSelect: document.querySelector("#style-select"),
  input: document.querySelector("#input"),
  example: document.querySelector("#example"),
  output: document.querySelector("#output"),
  loadExample: document.querySelector("#load-example"),
  copyOutput: document.querySelector("#copy-output"),
  status: document.querySelector("#status"),
};

function normalizeParagraphs(text) {
  return text
    .replace(/\r\n/g, "\n")
    .split(/\n{2,}/)
    .map((paragraph) => paragraph.replace(/\s+/g, " ").trim())
    .filter(Boolean);
}

function splitLongWord(word, width) {
  const chunks = [];

  for (let index = 0; index < word.length; index += width) {
    chunks.push(word.slice(index, index + width));
  }

  return chunks;
}

function wordsForWidth(text, width) {
  return text
    .split(/\s+/)
    .filter(Boolean)
    .flatMap((word) => {
      if (word.length <= width) {
        return [word];
      }

      return splitLongWord(word, width);
    });
}

function wrapWords(words, width) {
  const lines = [];
  let line = [];
  let lineLength = 0;

  for (const word of words) {
    const candidateLength = line.length === 0 ? word.length : lineLength + 1 + word.length;

    if (candidateLength <= width) {
      line.push(word);
      lineLength = candidateLength;
      continue;
    }

    lines.push(line);
    line = [word];
    lineLength = word.length;
  }

  if (line.length > 0) {
    lines.push(line);
  }

  return lines;
}

function wrapParagraph(text, width) {
  return wrapWords(wordsForWidth(text, width), width).map((line) => line.join(" "));
}

function padRight(text, width) {
  return `${text}${" ".repeat(Math.max(width - text.length, 0))}`;
}

function centerLine(text, width) {
  const trimmed = text.trim();

  if (trimmed.length >= width) {
    return trimmed;
  }

  const totalPadding = width - trimmed.length;
  const leftPadding = Math.floor(totalPadding / 2);
  const rightPadding = totalPadding - leftPadding;
  return `${" ".repeat(leftPadding)}${trimmed}${" ".repeat(rightPadding)}`;
}

function justifyWords(words, width, isLastLine) {
  if (words.length === 0) {
    return "";
  }

  if (words.length === 1 || isLastLine) {
    return words.join(" ");
  }

  const letters = words.reduce((sum, word) => sum + word.length, 0);
  const gaps = words.length - 1;
  const spaces = width - letters;
  const baseGap = Math.floor(spaces / gaps);
  const remainder = spaces % gaps;

  return words
    .slice(0, -1)
    .map((word, index) => `${word}${" ".repeat(baseGap + (index < remainder ? 1 : 0))}`)
    .join("") + words[words.length - 1];
}

function formatMobileBorder4(text, settings) {
  const paragraphs = normalizeParagraphs(text);
  const indent = " ".repeat(settings.leftPadding);
  const contentWidth = settings.totalWidth - settings.leftPadding;

  if (paragraphs.length === 0) {
    return "";
  }

  return paragraphs
    .map((paragraph) =>
      wrapParagraph(paragraph, contentWidth)
        .map((line) => `${indent}${line}`)
        .join("\n")
    )
    .join("\n\n");
}

function formatPlainText75(text, settings) {
  const paragraphs = normalizeParagraphs(text);

  if (paragraphs.length === 0) {
    return "";
  }

  return paragraphs
    .map((paragraph) => {
      const lines = wrapWords(wordsForWidth(paragraph, settings.totalWidth), settings.totalWidth);

      return lines
        .map((words, lineIndex) =>
          settings.justify
            ? justifyWords(words, settings.totalWidth, lineIndex === lines.length - 1)
            : words.join(" ")
        )
        .join("\n");
    })
    .join("\n\n");
}

function formatStarredBox75(text, settings) {
  const paragraphs = normalizeParagraphs(text);

  if (paragraphs.length === 0) {
    return "";
  }

  const frameWidth = settings.totalWidth - settings.sideLeft.length - settings.sideRight.length;
  const textWidth = frameWidth - settings.margin * 2;
  const sidePadding = " ".repeat(settings.margin);
  const blankLine = `${settings.sideLeft}${" ".repeat(frameWidth)}${settings.sideRight}`;
  const borderLine = `(${"*".repeat(settings.totalWidth - 2)})`;
  const boxedLines = [borderLine, blankLine];

  paragraphs.forEach((paragraph, paragraphIndex) => {
    const lines = wrapWords(wordsForWidth(paragraph, textWidth), textWidth);

    lines.forEach((words, lineIndex) => {
      const content = justifyWords(words, textWidth, lineIndex === lines.length - 1);
      boxedLines.push(`${settings.sideLeft}${sidePadding}${padRight(content, textWidth)}${sidePadding}${settings.sideRight}`);
    });

    if (paragraphIndex < paragraphs.length - 1) {
      boxedLines.push(blankLine);
    }
  });

  boxedLines.push(blankLine, borderLine);
  return boxedLines.join("\n");
}

function formatCenteredBox75(text, settings) {
  const paragraphs = normalizeParagraphs(text);

  if (paragraphs.length === 0) {
    return "";
  }

  const frameWidth = settings.totalWidth - settings.sideLeft.length - settings.sideRight.length;
  const textWidth = frameWidth - settings.margin * 2;
  const sidePadding = " ".repeat(settings.margin);
  const blankLine = `${settings.sideLeft}${" ".repeat(frameWidth)}${settings.sideRight}`;
  const borderLine = `(${"*".repeat(settings.totalWidth - 2)})`;
  const boxedLines = [borderLine, blankLine];

  paragraphs.forEach((paragraph, paragraphIndex) => {
    const lines = wrapParagraph(paragraph, textWidth);

    lines.forEach((line) => {
      const content = centerLine(line, textWidth);
      boxedLines.push(`${settings.sideLeft}${sidePadding}${content}${sidePadding}${settings.sideRight}`);
    });

    if (paragraphIndex < paragraphs.length - 1) {
      boxedLines.push(blankLine);
    }
  });

  boxedLines.push(blankLine, borderLine);
  return boxedLines.join("\n");
}

function formatText(styleId, text) {
  const style = styles[styleId];

  if (!style) {
    return text;
  }

  switch (style.formatter) {
    case "mobileBorder4":
      return formatMobileBorder4(text, style.settings);
    case "plain75":
    case "plainJustified75":
      return formatPlainText75(text, style.settings);
    case "starredBox75":
      return formatStarredBox75(text, style.settings);
    case "centeredBox75":
      return formatCenteredBox75(text, style.settings);
    default:
      return text;
  }
}

function setStatus(message) {
  elements.status.textContent = message;
}

function currentStyle() {
  return styles[elements.styleSelect.value];
}

function refreshExample() {
  const styleId = elements.styleSelect.value;
  const style = currentStyle();
  elements.example.value = formatText(styleId, style.exampleInput);
}

function refreshOutput() {
  const styleId = elements.styleSelect.value;
  elements.output.value = formatText(styleId, elements.input.value);
}

async function copyOutput() {
  const { output } = elements;
  const value = output.value;

  if (!value) {
    setStatus("Nothing to copy.");
    return;
  }

  try {
    await navigator.clipboard.writeText(value);
    setStatus("Output copied.");
  } catch (_error) {
    output.focus();
    output.select();
    document.execCommand("copy");
    setStatus("Output copied.");
  }
}

function loadExample() {
  const style = currentStyle();
  elements.input.value = style.exampleInput;
  refreshOutput();
  setStatus("Example loaded into input.");
}

function initializeStyles() {
  const options = Object.entries(styles).map(([id, style]) => {
    const option = document.createElement("option");
    option.value = id;
    option.textContent = style.label;
    return option;
  });

  elements.styleSelect.append(...options);
  elements.styleSelect.value = Object.keys(styles)[0];
}

function initialize() {
  initializeStyles();
  refreshExample();
  refreshOutput();

  elements.styleSelect.addEventListener("change", () => {
    refreshExample();
    refreshOutput();
    setStatus("Style updated.");
  });

  elements.input.addEventListener("input", () => {
    refreshOutput();
    setStatus("Output refreshed.");
  });

  elements.loadExample.addEventListener("click", loadExample);
  elements.copyOutput.addEventListener("click", copyOutput);
}

initialize();
